CC=gcc

CFLAGS=`pkg-config --cflags fuse openssl`
LDFLAGS=`pkg-config --libs fuse openssl`

PROGNAME=monocrypt_xts

all:
	$(CC) -pedantic -Wall $(CFLAGS) $(LDFLAGS) -o $(PROGNAME) $(PROGNAME).c
