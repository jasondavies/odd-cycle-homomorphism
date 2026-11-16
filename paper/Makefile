LATEXMK ?= latexmk
MANUSCRIPT := odd-cycle-homomorphism

.PHONY: all clean
all: $(MANUSCRIPT).pdf

$(MANUSCRIPT).pdf: $(MANUSCRIPT).tex
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $<

clean:
	$(LATEXMK) -c $(MANUSCRIPT).tex
