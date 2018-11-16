#
# Students' Makefile for the Malloc Project
#
CC = gcc
CFLAGS = -Wall -O2 -m64

OBJS = mdriver.o mm.o memlib.o fsecs.o

mdriver: $(OBJS)
	$(CC) $(CFLAGS) -o mdriver $(OBJS)

mdriver.o: mdriver.c fsecs.h memlib.h config.h mm.h
memlib.o: memlib.c memlib.h
mm.o: mm.c mm.h memlib.h
fsecs.o: fsecs.c fsecs.h config.h

clean:
	rm -f *~ *.o mdriver

