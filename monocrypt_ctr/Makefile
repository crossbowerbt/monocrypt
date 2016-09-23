CC=gcc

CFLAGS=`pkg-config --cflags fuse openssl`
LDFLAGS=`pkg-config --libs fuse openssl`

PROGNAME=monocrypt_ctr

all:
	$(CC) $(CFLAGS) $(LDFLAGS) -o $(PROGNAME) $(PROGNAME).c
