CFLAGS	= -g -DDEBUG
CC      = gcc $(CFLAGS)

all: ool socket.so math.so

ool: scanner.l grammar.y ool.c
	bison -d -t grammar.y
	flex -d -o scanner.c scanner.l
	$(CC) -c scanner.c
	$(CC) -c grammar.tab.c
	$(CC) -Wall -Wno-parentheses -Wno-unused-parameter -Wno-missing-field-initializers -W -c ool.c
	$(CC) -Wl,--export-dynamic -o ool scanner.o grammar.tab.o ool.o -ldl

socket.so: socket.c
	$(CC) -fPIC -c socket.c
	$(CC) -shared -Wl,-soname,socket.so -o socket.so socket.o

math.so: math.c
	$(CC) -fPIC -c math.c
	$(CC) -shared -Wl,-soname,math.so -o math.so math.o -lm

clean:
	rm -f *~ ool *.o scanner.c grammar.tab.* *.so