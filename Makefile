.PHONY: 	all clean byte native profile debug sanity test

OCB_FLAGS   = -use-ocamlfind -use-menhir -I src -I lib # uses menhir
OCB = ocamlbuild $(OCB_FLAGS)

all: native # profile debug

clean:
	$(OCB) -clean

native: sanity
	$(OCB) main.native

byte: sanity
	$(OCB) main.byte

test: sanity
	$(OCB) test.native

profile: sanity
	$(OCB) -tag profile main.native

debug: sanity
	$(OCB) -tag debug main.byte


# check that menhir is installed, use "opam install menhir"
sanity:
	which menhir

graph: native
	./main.native < $(test) > test.dot
	dot -Tsvg -otest.svg test.dot
	eog test.svg
