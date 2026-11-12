# Graph homomorphism parameterized by both treewidths

A reduction from binary longest common subsequence to simple undirected graph
homomorphism, with a Lean 4 proof of the complete combinatorial reduction.
The checked construction has source treewidth at most `max(2k,12)` and target
treewidth at most `12`, where `k` is the number of input strings.

**Status: Lean checks decision equivalence, both width bounds, all trivial input
cases, and polynomial finite output size.** The main theorem is
[`LCSInstance.full_reduction`](TreewidthHom/FullReduction.lean).
All 54 principal-declaration axiom audits pass without proof admissions.

A formal machine-level running-time proof and parameterized-complexity framework
are still absent. The written polynomial-time argument and Pietrzak's published
LCS hardness theorem yield W[1]-hardness; that complexity conclusion is **not a
Lean theorem in this repository**. The written proof also gives the sharper
source bound `max(k+1,12)` and a sharper size bound than the checked construction.
[FORMALIZATION.md](FORMALIZATION.md) records the exact boundary.

**Prior work:** W[1]-hardness was already announced in
[Amarilli's comment of 2025-05-30](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth#comment124806_34877).
The relationship between this reduction and that work, and any novelty of this
proof, have not been established. This repository makes no priority claim.

- [Problem statement and public status](PROBLEM.md)
- [Written solution, including all reduction stages](SOLUTION.md)
- [Lean theorem map and remaining obligations](FORMALIZATION.md)
- [Executable reduction](scripts/bounded_width_hom_hardness.py)

The construction first expresses a shared subsequence using padded paths in a
fixed relational schema. Typed incidence graphs remove relation names; distinct
prime cycles enforce types; an asymmetric undirected gadget encodes directions.
Explicit decompositions bound the widths at each step.

## Reproduce

Requires [elan](https://github.com/leanprover/elan) and Python 3. Lean **4.35.0**
and mathlib **v4.35.0** are pinned, including exact dependency revisions.

```sh
lake exe cache get
lake build
python3 scripts/check_formalization.py
python3 scripts/regenerate_quotient_certificates.py --check
python3 scripts/run_bounded_width_hom_checks.py
```

The Lean audit rejects proof admissions and nonstandard axiom dependencies.
The gadget certificate is evaluated by Lean's kernel; it does not use
`native_decide`. The Python checks independently exercise the executable
construction, but finite tests are not proofs of the general reduction.
Recorded reports are in [sources](sources/).

## Provenance

Extracted from a3nm-032 in `../open-problems`; written proof dated 2026-10-25,
Lean development begun 2026-11-12. Developed with AI assistance; independent
review remains pending. Binary LCS hardness is due to Pietrzak. The direction
gadget is credited to Hell–Nešetřil via Eleftheriadis. See the citations in
[SOLUTION.md](SOLUTION.md). This is separate from the minimum-edge treewidth
problem.
