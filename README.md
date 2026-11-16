# Graph homomorphism to an odd cycle is hard for bounded treewidth

This repository answers the question
[Complexity of the homomorphism problem parameterized by treewidth](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth):
graph homomorphism is not fixed-parameter tractable in the treewidths of the two
graphs unless FPT = W[1]. The proof is in the paper
[The parameterized complexity of homomorphism to an odd cycle](paper/odd-cycle-homomorphism.pdf).

## Results

Deciding whether a graph `G` has a homomorphism to an odd cycle `C_n`, with `n`
part of the input, is:

| Parameter | Result |
| --- | --- |
| Width of a supplied path decomposition of `G` | XNLP-complete |
| Width of a supplied tree decomposition of `G` | XALP-complete |
| Feedback vertex number of `G` | W[3]-hard; in W[P] |

The hardness results also hold without supplied decompositions, and
XNLP-hardness implies W[t]-hardness for every t. The target has treewidth 2,
which is best possible: homomorphism into a forest is polynomial. The hard
sources can be taken 2-degenerate and of arbitrarily large constant girth.

All three results come from one reduction from List Coloring, which raises
treewidth, pathwidth and feedback vertex number by constants.
[ODD_CYCLE.md](ODD_CYCLE.md) summarises the construction.

## What is machine-checked

The reduction is checked in Lean 4
([`OddCycle.ListReduction.reduction`](TreewidthHom/ListTheorem.lean)): a list
colouring exists exactly when `G → C_n`, and the source has

- treewidth at most `max(w+2, 4)` for an input of treewidth `w`;
- pathwidth at most `p+6` for an input of pathwidth `p`;
- a feedback vertex set of size `|S|+2` for an input feedback vertex set `S`;
- polynomial size, with target pathwidth at most 2.

The hardness of List Coloring, the time and space bounds of the reduction and
of the membership algorithms, the complexity-class conclusions, degeneracy and
girth are **not Lean theorems**; the paper proves or cites them.
[FORMALIZATION.md](FORMALIZATION.md) states the boundary.

## Reproduce

Requires [elan](https://github.com/leanprover/elan), Python 3 and, for the
paper, latexmk. Lean 4.35.0 and mathlib v4.35.0 are pinned.

```sh
lake exe cache get
python3 scripts/check_formalization.py   # build, then audit 37 declarations
python3 scripts/run_list_cycle_checks.py # 841 finite instances
python3 -m unittest discover -s scripts -p 'test_*.py' # verifier regressions
make -C paper
```

The audit rejects proof admissions and any axiom other than `propext`,
`Classical.choice` and `Quot.sound`. Finite checks are not proofs. Reports are
in [sources](sources/).

## Prior work

W[1]-hardness of the original question was announced in
[Amarilli's May 2025 comment](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth#comment124806_34877),
without a public proof that we could find. Overlap with that work and novelty
have not been established, and this repository makes no priority claim. See
[PROBLEM.md](PROBLEM.md) for the question and its status. Development and
drafting used AI assistance; independent review is pending.
