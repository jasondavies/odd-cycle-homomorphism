# Parameterised complexity of graph homomorphism to odd cycles

This repository contains the paper, Lean proofs, and executable checks for
homomorphism from a graph `G` to an odd cycle `C_n`.
The odd target length `n ≥ 5` is part of the input and may be given in binary.

Read the paper: **[Parameterised complexity of graph homomorphism to odd cycles](paper/odd-cycle-homomorphism.pdf)**.
For a short explanation of the gadgets and structural bounds, see
[CONSTRUCTION.md](CONSTRUCTION.md).
The [Palomar submission guide](PALOMAR.md) describes the independent statement,
Comparator checks, and final snapshot requirements.

## Results

| Parameter | Result |
| --- | --- |
| Width of a supplied path decomposition of `G` | XNLP-complete |
| Width of a supplied tree decomposition of `G` | XALP-complete |
| Feedback vertex number of `G` | W[SAT]-hard; in W[P] |

All three hardness statements follow from one reduction from List Colouring,
which increases treewidth, pathwidth, and feedback vertex number by constants.
For padded inputs containing an edge, treewidth and feedback vertex number
increase by exactly two.
Membership follows from separate arguments: the XNLP and XALP membership
statements require supplied decompositions; the W[P] upper bound does not.

The hardness results also hold without supplied decompositions. Every target
has treewidth and pathwidth two; the source width varies with the parameter.
Homomorphism to targets of treewidth at most one is polynomial-time decidable.
For each fixed `0 < ε < 1`, the hard sources can be connected and 2-degenerate
with girth `Ω(N^(1−ε))` on `N` vertices.

The same three classifications hold for recognising graphs whose core is an
odd cycle, with no target supplied. For a nonbipartite graph this asks whether
it maps to its own shortest odd cycle; the paper gives the equivalent
circular-colouring formulation.

Both problems admit an algorithm taking `2^O(r)` time up to polynomial factors,
where `r` is the feedback edge number. The same algorithm tests circular-clique
thresholds given in binary and computes the exact circular chromatic number.
This gives fixed-parameter tractability
for feedback vertex number plus maximum degree and for the ratio of order to
girth. Both problems are polynomial-time decidable at girth `Ω(N log log N / log N)`.

The [companion note on long odd cycles](paper/long-odd-cycles.pdf) gives a
deterministic algorithm with running time $2^{O(N/\ell)}$ up to polynomial
factors for a target of length $\ell$. Core recognition is therefore polynomial
at odd girth $\Omega(N/\log N)$, even when short even cycles are present.

This answers the [treewidth question](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth):
homomorphism parameterised by the maximum of the two input treewidths is
W[1]-hard, and hence not fixed-parameter tractable unless FPT = W[1].
See the prior-work acknowledgement below.

## What Lean checks

The central theorem, [`ListReduction.reduction`](TreewidthHom/ListTheorem.lean),
checks that a list colouring exists exactly when `G → C_n`, together with:

- source treewidth at most `max(w+2, 3)` for input treewidth `w`;
- source pathwidth at most `p+6` for input pathwidth `p`;
- a feedback vertex set of size `|S|+2` for an input feedback vertex set `S`;
- polynomial source size and target pathwidth at most two.

[`ListReduction.parameter_reduction`](TreewidthHom/Parameters.lean) states the
same bounds for treewidth, pathwidth, and feedback vertex number as numbers,
and adds that the source is 2-degenerate, has girth at least `n`, and is
connected when every list omits a colour. Lean also checks the correctness
arguments behind the three membership algorithms, but not their resource bounds.

[`ListReduction.exact_parameter_transfer`](TreewidthHom/ListExact.lean) checks
the matching treewidth and feedback-number lower bounds under palette padding
and an input edge. The pathwidth lower bound also holds for nonempty edgeless
inputs. Lean checks target capping and the target-free odd-cycle-core reduction,
including the general equivalence with mapping to a shortest odd cycle.
Finite graphs admit finite-index tree certificates of the same width.
[ListCertificates](TreewidthHom/ListCertificates.lean) bounds the output tree
and path bag counts polynomially in the input bag count, vertex count and
numeric target length.
[WeightedFormula](TreewidthHom/WeightedFormula.lean) checks that a formula is true
under a fixed selector assignment exactly when the assignment extends to a proper
list colouring. [WeightedCycle](TreewidthHom/WeightedCycle.lean) composes this
with the cycle construction, proves both decision equivalences for one graph,
and exhibits a feedback vertex set of size `k+2`. For nonempty list inputs of
order at most `n`, Lean also proves exact girth `n` and at most `4*n^3` output vertices.

Lean also checks the [subdivision projection](TreewidthHom/OddSubdivision.lean) and
the [walk interval](TreewidthHom/CycleWalkInterval.lean) used by the feedback-edge
algorithm. The graph-level amplification and the general circular-clique algorithm are
proved in the main manuscript. The long-target algorithm is proved in the companion note.

The circular-chromatic-number interpretation, complexity classifications, and
machine resource bounds remain outside Lean.
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

The Lean audit builds the library and checks 117 declarations. The finite suite
checks 841 instances; the regression tests cover validation and optimised
Python execution. Both verification scripts write JSON reports to
[reports/](reports/). Finite checks corroborate the construction; they do not
replace the proofs.

[GitHub Actions](.github/workflows/verify.yml) runs the Lean audit and Palomar
Comparator, the finite suite, and regression tests in normal and optimised Python
on pushes and pull requests. The generated Lean audit is retained as a workflow
artifact tied to the checked commit.

To rebuild both PDFs, run `make -C paper`; see [paper/README.md](paper/README.md)
for LaTeX requirements.

## Repository guide

| Path | Purpose |
| --- | --- |
| [paper/](paper/) | Both manuscript sources, vector diagram, and compiled PDFs |
| [CONSTRUCTION.md](CONSTRUCTION.md) | Short mathematical overview |
| [FORMALIZATION.md](FORMALIZATION.md) | Lean theorem map, scope, and audit details |
| [TreewidthHom/](TreewidthHom/) | Lean proofs; [TreewidthHom.lean](TreewidthHom.lean) is the library entry point |
| [AxiomAudit.lean](AxiomAudit.lean) | Declarations inspected by the audit |
| [Challenge.lean](Challenge.lean), [Solution.lean](Solution.lean) | Independent Palomar statement and proved counterpart |
| [formalization.yaml](formalization.yaml), [comparator.json](comparator.json) | Submission metadata and comparison configuration |
| [scripts/](scripts/) | Executable construction, finite checks, and verification tools |
| [reports/](reports/) | Generated verification results, retained for inspection |

## Prior work and attribution

The original question appears on [Amarilli's research-question list](https://a3nm.net/work/research/questions/#complexity-of-query-evaluation-parameterized-by-treewidth)
and in the graph-homomorphism formulation linked above.
[Amarilli's May 2025 comment](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth#comment124806_34877)
reported workshop reductions indicating W[1]-hardness. Amarilli later clarified
in personal communication that the reduction from $k$-Clique has source
pathwidth $k$ and target pathwidth two. This already gives W[1]-hardness
parameterised by source pathwidth for targets of pathwidth two. Our List
Colouring reduction gives XNLP-completeness for supplied path decompositions
and XALP-completeness for supplied tree decompositions with odd-cycle targets.
The paper cites the published List Colouring results used in the reduction.
Development and drafting used AI assistance; the paper describes the scope
and review status.

## Licence

This repository is licensed under [Apache-2.0](LICENSE). Dependencies and cited
works retain their own licences.
