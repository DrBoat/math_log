.PHONY: all run clean

OCAMLC=ocamlopt
DEL=rm -f

all: main

run: main
	./main

main: src/main.ml
	cd src && $(OCAMLC) main.ml -o ../main

clean:
	cd src && $(DEL) *.c* *.o*
	$(DEL) main