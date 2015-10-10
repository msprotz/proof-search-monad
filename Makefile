.PHONY: all

all:
	-rm proofSearchMonad.native
	ocamlbuild -I lib/ proofSearchMonad.native

clean:
	ocamlbuild -clean
