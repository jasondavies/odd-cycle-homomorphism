LATEXMK ?= latexmk
MANUSCRIPTS := odd-cycle-homomorphism long-odd-cycles

.PHONY: all clean
all: $(addsuffix .pdf,$(MANUSCRIPTS))

%.pdf: %.tex
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $<

clean:
	$(LATEXMK) -c $(addsuffix .tex,$(MANUSCRIPTS))
