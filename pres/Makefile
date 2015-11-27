.PHONY: all %.pdf
.FORCE:

export MZHOME=$(HOME)/Code/mezzo-private
export TEXINPUTS=$(MZHOME):$(MZHOME)/papers/common:$(MZHOME)/talks/common:.:
export BIBINPUTS=$(MZHOME)/papers/common:$(MZHOME)/talks/common:.:

%.pdf: .FORCE
	latexmk -pdf $*.tex

all: pres.pdf

preview:
	latexmk -pdf -pvc pres.tex

clean:
	latexmk -c

mrproper: clean
	cat ../.gitignore | xargs -I@ sh -c "rm @"
