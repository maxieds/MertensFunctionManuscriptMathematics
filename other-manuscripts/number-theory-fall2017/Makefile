CC=g++
CFLAGS=-g -O2 -Wall
LD=g++
LDFLAGS=-g -O2 -Wall
EXE=verify
OBJS=verify105.o

default: $(OBJS)
	$(LD) -o $(EXE) $(OBJS) $(LDFLAGS)

clean:
	rm ./*.o ./*.code $(EXE)

verify105.o: verify105.cpp
	$(CC) $(CFLAGS) -c verify105.cpp
