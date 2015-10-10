.PHONY: all tags

all:
ifeq ($(OS),Windows_NT)
	# Workaroud a bug in OCamlbuild and mtimes on Windows.
	-rm proofSearchMonad.native
endif
	ocamlbuild -I lib/ proofSearchMonad.native

clean:
	ocamlbuild -clean

test: all
	./proofSearchMonad.native

tags:
	find . -path ./_build -prune -o -iname '*.ml*' | xargs ctags
