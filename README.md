# Graph homomorphism parameterized by both treewidths

A written reduction from binary longest common subsequence to simple undirected
graph homomorphism, with a Lean 4 formalisation of several proof components.
The reduction has source treewidth at most `max(k+1,12)` and target treewidth at
most `12`, where `k` is the number of input strings. Together with Pietrzak's
LCS hardness theorem, the written argument gives W[1]-hardness.

**Status: the written proof is complete; the Lean formalisation is partial.**
Lean now verifies the complete relational-to-simple-graph homomorphism
correspondence: typed incidence, prime-cycle colour erasure, and undirected
gadget replacement. This includes confinement for arbitrary assemblies and the
last stage's `max(k,12)` width bound and exact vertex count. The LCS relational
front end, some earlier width/size bounds, and an end-to-end W[1]-hardness theorem
are **not yet formalised**. [FORMALIZATION.md](FORMALIZATION.md) records the boundary.

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
