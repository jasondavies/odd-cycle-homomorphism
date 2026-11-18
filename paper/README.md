# Manuscripts

- [Parameterised complexity of graph homomorphism to odd cycles](odd-cycle-homomorphism.pdf) gives the structural hardness results and the feedback-edge algorithm for exact circular colouring. [LaTeX source](odd-cycle-homomorphism.tex)
- [Homomorphisms to long odd cycles in time exponential in the order-to-length ratio](long-odd-cycles.pdf) gives the spanning-tree algorithm and its consequence for recognition at large odd girth. [LaTeX source](long-odd-cycles.tex)

Run `make -C paper` from the repository root to build both PDFs. To build one,
use its filename as the target. The build requires `latexmk` and a LaTeX
installation with the AMS, Latin Modern and PGF/TikZ packages.
`make -C paper clean` removes auxiliary files and retains the PDFs.

For proof verification and executable checks, see the
[root README](../README.md#reproduce) and [formalisation guide](../FORMALIZATION.md).
