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
   Debug
*/
//#define DEBUG

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

#define BLOCK_BITS 128
#define BLOCK_SIZE (BLOCK_BITS/8)

static uint64_t main_key[KEY_BITS/64] = { 0 };
static uint64_t nonce[BLOCK_BITS/64] = { 0 };

/*
    Cryptographic primitives
*/

#define passphrase_hash prim_passphrase_sha256

#define enc_block prim_enc_block_aes256
#define dec_block prim_dec_block_aes256

static void
prim_passphrase_sha256(uint8_t digest[SHA256_DIGEST_LENGTH],
                       const uint8_t *passwd, size_t passwdsz,
                       const uint8_t *salt, size_t saltsz)
{
    SHA256_CTX ctx;

    SHA256_Init(&ctx);
    SHA256_Update(&ctx, passwd, passwdsz);
    SHA256_Update(&ctx, salt, saltsz);
    SHA256_Final(digest, &ctx);
}

static void
prim_enc_block_aes256(uint8_t cipher[BLOCK_SIZE],
              const uint8_t plain[BLOCK_SIZE],
              const uint8_t key[KEY_SIZE])
{
    AES_KEY aes_key;

    AES_set_encrypt_key(key, KEY_BITS, &aes_key);
    AES_encrypt(plain, cipher, &aes_key);
}

static void
prim_dec_block_aes256(const uint8_t cipher[BLOCK_SIZE],
              uint8_t plain[BLOCK_SIZE],
              const uint8_t key[KEY_SIZE])
{
    AES_KEY aes_key;

    AES_set_decrypt_key(key, KEY_BITS, &aes_key);
    AES_decrypt(cipher, plain, &aes_key);
}

/*
    CTR (counter) mode utilities
*/

static void
ctr_key_for_block(uint8_t block_key[BLOCK_SIZE],
          const uint64_t main_key[KEY_BITS/64],
          const uint64_t nonce[BLOCK_BITS/64],
          uint64_t block_num)
{
    uint64_t nonce_indexed[BLOCK_BITS/64] = {
    nonce[0], nonce[1] ^ htobe64(block_num)
    };

    enc_block(block_key, (const uint8_t *)nonce_indexed, (const uint8_t *)main_key);
}

static void
ctr_xor_block(uint64_t block[BLOCK_BITS/64], const uint64_t block_key[BLOCK_BITS/64])
{
    register int i;

    for(i = 0; i < BLOCK_BITS/64; i++) {
    block[i] ^= block_key[i];
    }
}

/*
    Decryption and encryption of sequences of blocks
*/

static void
enc_dec_block_sequence(uint8_t *blocks, size_t size,
               const uint64_t main_key[KEY_BITS/64],
               const uint64_t nonce[BLOCK_BITS/64],
               uint64_t first_block_num)
{
    uint8_t block_key[BLOCK_SIZE];
    register int i;

    assert(size % (BLOCK_SIZE) == 0);

    for(i = 0; i < size; i += (BLOCK_SIZE)) {
    ctr_key_for_block(block_key, main_key, nonce, first_block_num + (i/(BLOCK_SIZE)));
    ctr_xor_block((uint64_t *)&blocks[i], (uint64_t *)block_key);
    }
}

/*
    Input/Output functions
*/

#define MAX_BLOCK_SEQUENCE_SIZE ((BLOCK_SIZE)*256)

static int
read_block_sequence(uint8_t *blocks, size_t size,
             uint64_t first_block_num) {
    size_t ret = 0, count = 0;

    fseek(encrypted_fp, first_block_num * (BLOCK_SIZE), SEEK_SET);

    do {
        ret = fread(blocks + count, 1, size - count, encrypted_fp);
        if(ret == -1) return ret;

        count += ret;
    } while (count != size);

    return count;
}

static int
write_block_sequence(const uint8_t *blocks, size_t size,
             uint64_t first_block_num) {
    size_t ret = 0, count = 0;

    fseek(encrypted_fp, first_block_num * (BLOCK_SIZE), SEEK_SET);

    do {
        ret = fwrite(blocks + count, 1, size - count, encrypted_fp);
        if(ret == -1) return ret;

        count += ret;
    } while (count != size);

    return count;
}

/*
    FUSE functions
*/

#define PLAIN_FILENAME "plain"

static int
readdir_callback(const char *path, void *buf, fuse_fill_dir_t filler,
         off_t offset, struct fuse_file_info *fi) {
    (void) offset;
    (void) fi;

    filler(buf, ".", NULL, 0);
    filler(buf, "..", NULL, 0);

    filler(buf, PLAIN_FILENAME, NULL, 0);

    return 0;
}

static int
getattr_callback(const char *path, struct stat *stbuf) {
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
open_callback(const char *path, struct fuse_file_info *fi) {
    return 0;
}

static int
read_callback(const char *path, char *buf, size_t size,
          off_t offset, struct fuse_file_info *fi) {

#ifdef DEBUG
    fprintf(stderr, "read_callback(path=\"%s\", buf=0x%08x, size=%d, offset=%lld, fi=0x%08x)\n",
        path,  (int) buf, size,  offset,  (int) fi);
#endif

    if (strcmp(path, "/" PLAIN_FILENAME) == 0) {

        off_t len = encrypted_stat.st_size - sizeof(nonce);

    if (offset >= len) {
        return 0;
        }

    if (offset + size > len) {
        size = len - offset;
        if(!size) return 0;
    }

    if(size > MAX_BLOCK_SEQUENCE_SIZE) {
        size = MAX_BLOCK_SEQUENCE_SIZE;
    }

    /* allocate space for sequence */

    // we add an extra block to handle unaligned reads:
    uint8_t blocks[MAX_BLOCK_SEQUENCE_SIZE + (BLOCK_SIZE)];

    uint64_t first_block_num = offset / (BLOCK_SIZE);
        size_t seq_size = size + (offset % (BLOCK_SIZE));

    /* fill extra bytes to obtain a sequence length
       which is a multiple of the block size */

    if((offset + size) % (BLOCK_SIZE) != 0)
        seq_size += (BLOCK_SIZE) - ((offset + size) % (BLOCK_SIZE));

    /* read sequence of blocks */

    size_t ret = read_block_sequence(blocks, seq_size, first_block_num);
    if(ret != seq_size) {
        fprintf(stderr,
            "read_block_sequence(): read only %lu out of %lu bytes",
            ret, seq_size);
        return 0;
    }

    /* decrypt sequence of blocks */

    enc_dec_block_sequence(blocks, seq_size,
                   main_key, nonce, first_block_num);

    memcpy(buf, blocks + (offset % (BLOCK_SIZE)), size);

    return size;
    }

    return -ENOENT;
}

static int
write_callback(const char *path, const char *buf, size_t size,
           off_t offset, struct fuse_file_info *fi) {

#ifdef DEBUG
    fprintf(stderr, "write_callback(path=\"%s\", buf=0x%08x, size=%d, offset=%lld, fi=0x%08x)\n",
        path,  (int) buf, size,  offset,  (int) fi);
#endif

    if (strcmp(path, "/" PLAIN_FILENAME) == 0) {

        off_t len = encrypted_stat.st_size - sizeof(nonce);

    if (offset >= len) {
        return -1;
        }

    if (offset + size > len) {
        size = len - offset;
        if(!size) return -1;
    }

    if(size > MAX_BLOCK_SEQUENCE_SIZE) {
        size = MAX_BLOCK_SEQUENCE_SIZE;
    }

    /* allocate space for sequence */

    // we add an extra block to handle unaligned reads:
        uint8_t blocks[MAX_BLOCK_SEQUENCE_SIZE + (BLOCK_SIZE)];

    uint64_t first_block_num = offset / (BLOCK_SIZE);
        size_t seq_size = size + (offset % (BLOCK_SIZE));

    /* fill extra bytes to obtain a sequence length
       which is a multiple of the block size */

    if((offset + size) % (BLOCK_SIZE) != 0)
        seq_size += (BLOCK_SIZE) - ((offset + size) % (BLOCK_SIZE));

#ifdef DEBUG
        fprintf(stderr, "write_callback() params: seq_size=\"%d\", first_block=\"%d\"\n",
        seq_size, first_block_num);
#endif

    /* read sequence of blocks */

    size_t ret = read_block_sequence(blocks, seq_size, first_block_num);
    if(ret != seq_size) {
        fprintf(stderr,
            "read_block_sequence(): read only %lu out of %lu bytes",
            ret, seq_size);
        return -1;
    }

    /* decrypt sequence of blocks */

    enc_dec_block_sequence(blocks, seq_size,
                   main_key, nonce, first_block_num);

    memcpy(blocks + (offset % (BLOCK_SIZE)), buf, size);

    /* re-encrypt sequence */

    enc_dec_block_sequence(blocks, seq_size,
                   main_key, nonce, first_block_num);

    /* write it back in encrypted file */

    ret = write_block_sequence(blocks, seq_size, first_block_num);
    if(ret != seq_size) {
        fprintf(stderr,
            "write_block_sequence(): written only %lu out of %lu bytes",
            ret, seq_size);
        return -1;
    }

    return size;
    }

    return -ENOENT;
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
    fprintf(stderr, "usage: %s encrypted_file mount_point/ [-fsd]\n", argv[0]);
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

    if(encrypted_stat.st_size % (BLOCK_SIZE) != 0) {
    fprintf(stderr, "error: size of encrypted file \"%s\" must be a multiple of %d bytes (size of block)\n",
        encrypted_filename, BLOCK_SIZE);
    return 1;
    }

    /* read nonce from the end of encrypted file, and passphrase from user*/

    fseek(encrypted_fp, encrypted_stat.st_size - sizeof(nonce), SEEK_SET);
    fread(nonce, 1, sizeof(nonce), encrypted_fp);

    passphrase = getpass("Insert passphrase: ");

    /* generate main key from passphrase and nonce (nonce is used as salt) */

    passphrase_hash((uint8_t *)main_key, (uint8_t *) passphrase, strlen(passphrase), (uint8_t *)nonce, sizeof(nonce));

    /* cleanup */

    memset(passphrase, 0, strlen(passphrase));

    /* run fuse main procedure */

    return fuse_main(argc - 1, argv + 1, &callback_operations, NULL);
}
