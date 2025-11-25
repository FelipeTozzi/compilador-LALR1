CC = gcc
CFLAGS = -O2 -std=c99 -W -Wall

all: lalr1

lalr1: lalr1.c
	$(CC) $(CFLAGS) -o lalr1 lalr1.c

clean:
	rm -f lalr1 *.o
