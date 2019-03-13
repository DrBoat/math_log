.PHONY: all run clean

OCAMLC=ocamlc
PACKAGE=hw1.zip

ifeq ($(OS),Windows_NT)
	DEL=del /f
else
	DEL=rm -f
endif

all: main.exe

run: main.exe
	./main.exe

main.exe: src/main.ml
	cd src && $(OCAMLC) main.ml -o ../main.exe

clean:
	cd src && $(DEL) *.c* *.o*
	$(DEL) main.exe