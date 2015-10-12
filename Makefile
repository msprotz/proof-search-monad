.PHONY: all tags

FILES=example01 example02 #example03

all:
ifeq ($(OS),Windows_NT)
	# Workaroud a bug in OCamlbuild and mtimes on Windows.
	-rm $(addsuffix .native,$(FILES))
endif
	ocamlbuild -I lib/ $(addsuffix .native,$(FILES))

clean:
	ocamlbuild -clean

test: all
	$(addprefix ./, $(addsuffix .native &&, $(FILES))) true

tags:
	find . -path ./_build -prune -o -iname '*.ml*' | xargs ctags
