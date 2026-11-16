# Manuscript

[The parameterised complexity of homomorphism to an odd cycle](odd-cycle-homomorphism.pdf)
— [LaTeX source](odd-cycle-homomorphism.tex).

From the repository root:

```sh
make -C paper
```

Requires `latexmk` and a LaTeX installation with the AMS, Latin Modern, and
PGF/TikZ packages. The vector construction diagram is defined in the manuscript.
`make -C paper clean` removes auxiliary files and retains the PDF.

For proof verification and executable checks, see the
[root README](../README.md#reproduce) and [formalisation guide](../FORMALIZATION.md).
