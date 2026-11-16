# Manuscript

[odd-cycle-homomorphism.tex](odd-cycle-homomorphism.tex) is the manuscript
source; [odd-cycle-homomorphism.pdf](odd-cycle-homomorphism.pdf) is the compiled
draft. Its article layout, author block, inline bibliography, formalisation
appendix and AI disclosure follow `../../euclid-uniform-processes/paper/`.

Build from the repository root with:

```sh
make -C paper
```

This requires `latexmk` and a LaTeX installation with the standard AMS and
Latin Modern packages. `make -C paper clean` removes auxiliary files while
retaining the PDF.

The XNLP-completeness statement uses a **supplied source path decomposition**
and its width as parameter. The paper distinguishes the checked Lean
reduction theorems from the pathwidth and machine-resource arguments proved
in the text. It makes no priority claim over the previously announced
W[1]-hardness result. The author block is inherited from the example;
the disclosure does not assert independent human review of this draft.
