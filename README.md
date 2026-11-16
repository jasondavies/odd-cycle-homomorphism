# Homomorphism to an odd cycle

One reduction from List Colouring establishes the parameterised complexity of
deciding whether a graph `G` admits a homomorphism to an odd cycle `C_n`.
The target length `n` is part of the input, given explicitly or in unary.

Read the paper: **[The parameterised complexity of homomorphism to an odd cycle](paper/odd-cycle-homomorphism.pdf)**.
For a short explanation of the gadgets and structural bounds, see
[CONSTRUCTION.md](CONSTRUCTION.md).

## Results

| Parameter | Result |
| --- | --- |
| Width of a supplied path decomposition of `G` | XNLP-complete |
| Width of a supplied tree decomposition of `G` | XALP-complete |
| Feedback vertex number of `G` | W[3]-hard; in W[P] |

The hardness results also hold without supplied decompositions. Every target
has treewidth and pathwidth two; the source width varies with the parameter.
Homomorphism to targets of treewidth at most one is polynomial-time decidable.
The hard sources can be connected, 2-degenerate, and of arbitrarily large
prescribed constant girth.

This answers the [treewidth question](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth):
homomorphism parameterised by the maximum of the two input treewidths is
W[1]-hard, and hence not fixed-parameter tractable unless FPT = W[1].
See the prior-work acknowledgement below.

## What Lean checks

The central theorem, [`ListReduction.reduction`](TreewidthHom/ListTheorem.lean),
checks that a list colouring exists exactly when `G → C_n`, together with:

- source treewidth at most `max(w+2, 4)` for input treewidth `w`;
- source pathwidth at most `p+6` for input pathwidth `p`;
- a feedback vertex set of size `|S|+2` for an input feedback vertex set `S`;
- polynomial source size and target pathwidth at most two.

Complexity classifications, machine resource bounds, degeneracy, girth, and
connectedness are proved or cited in the paper, outside Lean.
[FORMALIZATION.md](FORMALIZATION.md) maps the statements to declarations and
explains the verification boundary.

## Reproduce

Run these commands from the repository root. Requires
[elan](https://github.com/leanprover/elan) and Python 3; the pinned versions are
Lean 4.35.0 and mathlib v4.35.0. Python uses only the standard library.

```sh
lake exe cache get
python3 scripts/check_formalization.py
python3 scripts/run_list_cycle_checks.py
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The Lean audit builds the library and checks 37 declarations. The finite suite
checks 841 instances; the regression tests cover validation and optimised
Python execution. Both verification scripts write JSON reports to
[reports/](reports/). Finite checks corroborate the construction; they do not
replace the proofs.

To rebuild the PDF, run `make -C paper`; see [paper/README.md](paper/README.md)
for LaTeX requirements.

## Repository guide

| Path | Purpose |
| --- | --- |
| [paper/](paper/) | Manuscript source, vector diagram, and compiled PDF |
| [CONSTRUCTION.md](CONSTRUCTION.md) | Short mathematical overview |
| [FORMALIZATION.md](FORMALIZATION.md) | Lean theorem map, scope, and audit details |
| [TreewidthHom/](TreewidthHom/) | Lean proofs; [TreewidthHom.lean](TreewidthHom.lean) is the library entry point |
| [AxiomAudit.lean](AxiomAudit.lean) | Declarations inspected by the audit |
| [scripts/](scripts/) | Executable construction, finite checks, and verification tools |
| [reports/](reports/) | Generated verification results, retained for inspection |

## Prior work and attribution

The original question appears on [Amarilli's research-question list](https://a3nm.net/work/research/questions/#complexity-of-query-evaluation-parameterized-by-treewidth)
and in the graph-homomorphism formulation linked above.
[Amarilli's May 2025 comment](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth#comment124806_34877)
already announced W[1]-hardness reductions. Their relationship to this
construction remains unresolved; this repository makes no priority claim.
The paper cites the published List Colouring results used in the reduction.
Development and drafting used AI assistance; the paper describes the scope
and review status.
