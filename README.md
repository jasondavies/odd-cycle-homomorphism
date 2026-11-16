# Graph homomorphism into an odd cycle, parameterized by source width

Deciding whether a graph maps homomorphically into an odd cycle given in the
input is hard for parameterized complexity classes when the parameter is the
treewidth or pathwidth of the source. The target has treewidth and pathwidth 2,
so graph homomorphism parameterized by both treewidths is hard even at target
treewidth 2. That is optimal: homomorphism into a forest is polynomial.

Two reductions are checked in Lean 4. Each proves decision equivalence, a width
bound for the source, width 2 for the target, and polynomial size.

| Reduction | From | Source width | Lean theorem |
| --- | --- | --- | --- |
| Plain | Multicoloured Clique, `k` classes | at most `k+2`; a feedback vertex set of `k+1` vertices | [`OddCycle.reduction_cycleGraph`](TreewidthHom/OddCycleReduction.lean) |
| Chained | Chained Multicoloured Clique, `k` colours, any number of layers | at most `2k+3` | [`OddCycle.Chained.reduction`](TreewidthHom/OddCycleChained.lean) |

With the published hardness of the two starting problems these give:

- W[1]-hardness parameterized by the feedback vertex number of the source;
- W[t]-hardness for every t, and XNLP-hardness, parameterized by its treewidth
  or pathwidth;
- XNLP-completeness when a path decomposition of the source is supplied.

**What Lean does and does not check.** Lean checks the two combinatorial
reductions. The hardness of the starting problems, the running time and space
of the reductions, membership in XNLP, and therefore the complexity conclusions
themselves are **not Lean theorems**. The pathwidth bounds are proved in prose
and checked on finite instances; Lean states treewidth. See
[FORMALIZATION.md](FORMALIZATION.md).

**Prior work:** W[1]-hardness of homomorphism parameterized by both treewidths
was announced in
[Amarilli's comment of 2025-05-30](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth#comment124806_34877).
The relationship between these reductions and that work, and any novelty, have
not been established. This repository makes no priority claim.

- [Problem statement and public status](PROBLEM.md)
- [The reductions and their proofs](ODD_CYCLE.md)
- [XNLP-completeness with a supplied path decomposition](XNLP_COMPLETENESS.md)
- [Lean theorem map and boundary](FORMALIZATION.md)

## Reproduce

Requires [elan](https://github.com/leanprover/elan) and Python 3. Lean **4.35.0**
and mathlib **v4.35.0** are pinned, including exact dependency revisions.

```sh
lake exe cache get
lake build
python3 scripts/check_formalization.py
python3 scripts/run_odd_cycle_checks.py
python3 scripts/run_odd_cycle_chained_checks.py
```

`check_formalization.py` builds the library, rejects proof admissions and
audits the principal declarations for nonstandard axioms. The two Python
runners build the source graphs and compare homomorphism existence with direct
search; they take several minutes each. Finite checks are not proofs. Recorded
reports are in [sources](sources/).

## History and provenance

Extracted from a3nm-032 in `../open-problems`. Developed with AI assistance;
independent review remains pending. An earlier version of this repository
proved hardness through longest common subsequence, with target treewidth 3,
together with an executable constructor and an abstract cost model. It was
removed once the odd-cycle reductions superseded its conclusions. It remains in
the git history at commit `4dfb72e`.
