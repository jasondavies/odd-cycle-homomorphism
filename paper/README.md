# Manuscript

[The parameterized complexity of homomorphism to an odd cycle](odd-cycle-homomorphism.pdf)
uses one reduction from List Coloring to establish XNLP-completeness for supplied
pathwidth, XALP-completeness for supplied treewidth, and W[3]-hardness for feedback
vertex number.

```sh
make -C paper
```

Requires `latexmk` and a LaTeX installation with the AMS, Latin Modern, and
PGF/TikZ packages. The construction diagram is vector artwork defined directly
in the manuscript; no external images or shell escape are needed.
`make -C paper clean` removes auxiliary files and retains the PDF.

The main reduction's equivalence, treewidth, pathwidth, feedback set transfer,
target pathwidth and polynomial size are Lean-checked. Complexity classes,
resource analysis, degeneracy and girth remain outside Lean, as specified in the
appendix. The draft preserves the prior May 2025 hardness announcement and makes
no priority claim. Independent review and assessment of novelty remain pending.
