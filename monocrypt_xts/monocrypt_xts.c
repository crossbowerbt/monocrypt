#define _BSD_SOURCE
#include <endian.h>

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <errno.h>

#include <sys/stat.h>
#include <assert.h>

#include <pwd.h>
#include <unistd.h>

#include <openssl/aes.h>
#include <openssl/sha.h>

#define FUSE_USE_VERSION 26
#include <fuse.h>

/*
  Modes of operation for the various functions in the program
*/

enum {
    MODE_DECRYPT = 0,
    MODE_ENCRYPT = 1
};

enum {
    MODE_READ = 0,
    MODE_WRITE = 1
};

/*
  Paths
*/

static char *encrypted_filename;
static struct stat encrypted_stat;
static FILE *encrypted_fp;

/*
  Crypto data
*/

#define KEY_BITS 256
#define KEY_SIZE (KEY_BITS/8)

#define NARROW_BLOCK_BITS 128
#define NARROW_BLOCK_SIZE (NARROW_BLOCK_BITS/8)

#define WIDE_BLOCK_BITS 4096
#define WIDE_BLOCK_SIZE (WIDE_BLOCK_BITS/8)

static uint8_t main_key[KEY_SIZE*2] = { 0 };
static uint8_t key1[KEY_SIZE] = { 0 };
static uint8_t key2[KEY_SIZE] = { 0 };

static uint8_t nonce[NARROW_BLOCK_SIZE] = { 0 };

/*
  Cryptographic primitives
*/

#define passphrase_hash prim_passphrase_sha512

#define enc_block prim_enc_block_aes256
#define dec_block prim_dec_block_aes256

static void
prim_passphrase_sha512(uint8_t digest[SHA512_DIGEST_LENGTH],
                       const uint8_t *passwd, size_t passwdsz,
                       const uint8_t *salt, size_t saltsz)
{
    SHA512_CTX ctx;

    SHA512_Init(&ctx);
    SHA512_Update(&ctx, passwd, passwdsz);
    SHA512_Update(&ctx, salt, saltsz);
    SHA512_Final(digest, &ctx);
}

static void
prim_enc_block_aes256(uint8_t cipher[NARROW_BLOCK_SIZE],
                      const uint8_t plain[NARROW_BLOCK_SIZE],
                      const uint8_t key[KEY_SIZE])
{
    AES_KEY aes_key;

    AES_set_encrypt_key(key, KEY_BITS, &aes_key);
    AES_encrypt(plain, cipher, &aes_key);
}

static void
prim_dec_block_aes256(const uint8_t cipher[NARROW_BLOCK_SIZE],
                      uint8_t plain[NARROW_BLOCK_SIZE],
                      const uint8_t key[KEY_SIZE])
{
    AES_KEY aes_key;

    AES_set_decrypt_key(key, KEY_BITS, &aes_key);
    AES_decrypt(cipher, plain, &aes_key);
}

/*
  XTS utilities
*/

static void
uint64_to_narrow_block(uint8_t dst[NARROW_BLOCK_SIZE],
                       uint64_t n)
{
    uint64_t *ptr;
    int i;

    n = htobe64(n);

    ptr = (uint64_t *) dst;

    for(i = 0; i < ((NARROW_BLOCK_SIZE/sizeof(*ptr))-1); i++) {
        ptr[i] = 0;
    }

    ptr[i] = n;
}

static void
xor_narrow_blocks(uint8_t dst[NARROW_BLOCK_SIZE],
                  uint8_t a[NARROW_BLOCK_SIZE],
                  uint8_t b[NARROW_BLOCK_SIZE])
{
    uint64_t *dst_ptr, *a_ptr, *b_ptr;
    int i;

    dst_ptr = (uint64_t *) dst;
    a_ptr = (uint64_t *) a;
    b_ptr = (uint64_t *) b;

    for(i = 0; i < (NARROW_BLOCK_SIZE/sizeof(*dst_ptr)); i++) {
        dst_ptr[i] = a_ptr[i] ^ b_ptr[i];
    }
}

static void
xex2(uint8_t l[NARROW_BLOCK_SIZE],
     const uint64_t j,
     const uint8_t key1[KEY_SIZE],
     const uint8_t key2[KEY_SIZE],
     uint8_t narrow_block[NARROW_BLOCK_SIZE],
     int mode)
{
    uint64_t alpha = 2;

    uint8_t delta[NARROW_BLOCK_SIZE];
    uint8_t tweak[NARROW_BLOCK_SIZE];

    // delta = l * (alpha ** j)

    uint64_to_narrow_block(tweak, alpha << j);
    xor_narrow_blocks(delta, l, tweak);

    // aes(key1, narrow_block ^ delta) ^ delta

    xor_narrow_blocks(narrow_block, narrow_block, delta);

    if(mode == MODE_ENCRYPT)
        enc_block(narrow_block, narrow_block, key1);
    else
        dec_block(narrow_block, narrow_block, key1);

    xor_narrow_blocks(narrow_block, narrow_block, delta);
}

/*
  Decryption and encryption of wide-blocks
*/

static void
xts(const uint64_t i,
    const uint8_t key1[KEY_SIZE],
    const uint8_t key2[KEY_SIZE],
    uint8_t wide_block[WIDE_BLOCK_SIZE],
    int mode)
{
    uint8_t l[NARROW_BLOCK_SIZE];
    int j;

    /* l = aes(key2, i) */

    uint64_to_narrow_block(l, i);
    enc_block(l, l, key2);

    for(j = 0; j < (WIDE_BLOCK_SIZE/NARROW_BLOCK_SIZE); j++) {

        uint8_t *narrow_block;

        narrow_block = &wide_block[j * NARROW_BLOCK_SIZE];
        xex2(l, j, key1, key2, narrow_block, mode);

    }
}

/*
  Decryption and encryption of sequences of wide-blocks
*/

static void
enc_dec_wide_block_sequence(uint8_t *blocks, size_t size,
                            const uint8_t key1[KEY_SIZE],
                            const uint8_t key2[KEY_SIZE],
                            uint64_t first_block_num,
                            int mode)
{
    uint64_t i;

    assert(size % (WIDE_BLOCK_SIZE) == 0);

    for(i = 0; i < (size/WIDE_BLOCK_SIZE); i++) {

        uint8_t *wide_block;

        wide_block = &blocks[i * WIDE_BLOCK_SIZE];
        xts(first_block_num + i, key1, key2, wide_block, mode);

    }
}

/*
  Input/Output functions
*/

#define MAX_WIDE_BLOCK_SEQUENCE_SIZE ((WIDE_BLOCK_SIZE)*8)

static int
read_block_sequence(uint8_t *blocks, size_t size,
                    uint64_t first_block_num)
{
    fseek(encrypted_fp, first_block_num * (WIDE_BLOCK_SIZE), SEEK_SET);
    return fread(blocks, 1, size, encrypted_fp);
}

static int
write_block_sequence(const uint8_t *blocks, size_t size,
                     uint64_t first_block_num)
{
    fseek(encrypted_fp, first_block_num * (WIDE_BLOCK_SIZE), SEEK_SET);
    return fwrite(blocks, 1, size, encrypted_fp);
}

/*
  FUSE functions
*/

#define PLAIN_FILENAME "plain"

static int
readdir_callback(const char *path, void *buf, fuse_fill_dir_t filler,
                 off_t offset, struct fuse_file_info *fi)
{
    (void) offset;
    (void) fi;

    filler(buf, ".", NULL, 0);
    filler(buf, "..", NULL, 0);

    filler(buf, PLAIN_FILENAME, NULL, 0);

    return 0;
}

static int
getattr_callback(const char *path, struct stat *stbuf)
{
    memset(stbuf, 0, sizeof(struct stat));

    if (strcmp(path, "/") == 0) {
        stbuf->st_mode = S_IFDIR | 0755;
        stbuf->st_nlink = 2;
        return 0;
    }

    if (strcmp(path, "/" PLAIN_FILENAME) == 0) {
        stbuf->st_mode = S_IFREG | 0777;
        stbuf->st_nlink = 1;
        stbuf->st_size = encrypted_stat.st_size - sizeof(nonce);
        return 0;
    }

    return -ENOENT;
}

static int
open_callback(const char *path, struct fuse_file_info *fi)
{
    return 0;
}

static int
read_write(const char *path, char *buf, size_t size,
           off_t offset, struct fuse_file_info *fi,
           int mode)
{
    if (strcmp(path, "/" PLAIN_FILENAME) == 0) {

        off_t len = encrypted_stat.st_size - sizeof(nonce);

        if (offset >= len) {
            return 0;
        }

        if (offset + size > len) {
            size = len - offset;
            if(!size) return 0;
        }

        if(size > MAX_WIDE_BLOCK_SEQUENCE_SIZE) {
            size = MAX_WIDE_BLOCK_SEQUENCE_SIZE;
        }

        /* allocate space for sequence */

        // we add an extra block to handle unaligned reads:
        uint8_t blocks[MAX_WIDE_BLOCK_SEQUENCE_SIZE + (WIDE_BLOCK_SIZE)];

        uint64_t first_block_num = offset / (WIDE_BLOCK_SIZE);
        size_t seq_size = size;

        /* fill extra bytes to obtain a sequence length
           which is a multiple of the block size */

        if(size % (WIDE_BLOCK_SIZE) != 0)
            seq_size += (WIDE_BLOCK_SIZE) - (size % (WIDE_BLOCK_SIZE));

        /* read sequence of blocks */

        size_t ret = read_block_sequence(blocks, seq_size, first_block_num);

        if(ret != seq_size) {
            fprintf(stderr,
                    "read_block_sequence(): read only %lu out of %lu bytes",
                    ret, seq_size);
            return 0;
        }

        /* READ operation */

        if(mode == MODE_READ) {

            /* decrypt sequence of blocks */

            enc_dec_wide_block_sequence(blocks, seq_size, key1, key2,
                                        first_block_num, MODE_DECRYPT);

            memcpy(buf, blocks + (offset % (WIDE_BLOCK_SIZE)), size);

        }

        /* WRITE operation */

        else {

            /* decrypt sequence of blocks */

            enc_dec_wide_block_sequence(blocks, seq_size, key1, key2,
                                        first_block_num, MODE_DECRYPT);

            memcpy(blocks + (offset % (WIDE_BLOCK_SIZE)), buf, size);

            /* re-encrypt sequence */

            enc_dec_wide_block_sequence(blocks, seq_size, key1, key2,
                                        first_block_num, MODE_ENCRYPT);

            /* write it back in encrypted file */

            ret = write_block_sequence(blocks, seq_size, first_block_num);

            if(ret != seq_size) {
                fprintf(stderr,
                        "write_block_sequence(): written only %lu out of %lu bytes",
                        ret, seq_size);
                return 0;
            }

        }

        return size;
    }

    return -ENOENT;
}

static int
read_callback(const char *path, char *buf, size_t size,
              off_t offset, struct fuse_file_info *fi)
{
    return read_write(path, buf, size, offset, fi, MODE_READ);
}

static int
write_callback(const char *path, const char *buf, size_t size,
               off_t offset, struct fuse_file_info *fi)
{
    return read_write(path, (char *) buf, size, offset, fi, MODE_WRITE);
}

static struct fuse_operations callback_operations = {
    .getattr = getattr_callback,
    .open = open_callback,
    .read = read_callback,
    .write = write_callback,
    .readdir = readdir_callback,
};

/*
  Main function
*/

int
main(int argc, char *argv[])
{
    char *passphrase = NULL;

    if(argc < 3) {
        fprintf(stderr, "usage: %s encrypted_file mount_point/\n", argv[0]);
        return 0;
    }

    encrypted_filename = argv[1];

    if((encrypted_fp = fopen(encrypted_filename, "rb+")) == NULL) {
        fprintf(stderr, "error: fopen() of file \"%s\" failed: %s\n", encrypted_filename, strerror(errno));
        return 1;
    }

    if(fstat(fileno(encrypted_fp), &encrypted_stat) != 0) {
        fprintf(stderr, "error: stat() of file \"%s\" failed: %s\n", encrypted_filename, strerror(errno));
        return 1;
    }

    if(encrypted_stat.st_size <= sizeof(nonce)) {
        fprintf(stderr, "error: size of encrypted file \"%s\" must be more than %lu bytes (size of nonce)\n",
                encrypted_filename, sizeof(nonce));
        return 1;
    }

    if(encrypted_stat.st_size % (WIDE_BLOCK_SIZE) != 0) {
        fprintf(stderr, "error: size of encrypted file \"%s\" must be a multiple of %d bytes (size of a wide block)\n",
                encrypted_filename, WIDE_BLOCK_SIZE);
        return 1;
    }

    /* read nonce from the end of encrypted file, and passphrase from user*/

    fseek(encrypted_fp, encrypted_stat.st_size - sizeof(nonce), SEEK_SET);
    fread(nonce, 1, sizeof(nonce), encrypted_fp);

    passphrase = getpass("Insert passphrase: ");

    /* generate main key from passphrase and nonce (nonce is used as salt) */

    passphrase_hash((uint8_t *)main_key, (uint8_t *)passphrase, strlen(passphrase),
                    (uint8_t *)nonce, sizeof(nonce));

    /* separate key1 and key2 */

    memcpy(key1, main_key, sizeof(key1));
    memcpy(key2, main_key + sizeof(key1), sizeof(key2));

    /* cleanup */

    memset(passphrase, 0, strlen(passphrase));

    /* run fuse main procedure */

    return fuse_main(argc - 1, argv + 1, &callback_operations, NULL);
}
