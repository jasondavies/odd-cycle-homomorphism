# Graph homomorphism parameterized by both treewidths

A reduction from binary longest common subsequence to simple undirected graph
homomorphism, with a Lean 4 proof of the complete combinatorial reduction.
The checked construction has source treewidth at most `max(2k,12)` and target
treewidth at most `12`, where `k` is the number of input strings.

**Status: the Lean constructor is executable and verified.**
[`Executable.compile_spec`](TreewidthHom/ExecutableReduction.lean) proves decision
equivalence, both width bounds, all input cases, and polynomial size for its
actual integer-numbered edge-list output. The earlier mathematical statement is
[`LCSInstance.full_reduction`](TreewidthHom/FullReduction.lean).
All 78 principal-declaration axiom audits pass without proof admissions.

Sparse direction-gadget serialization also has a checked quadratic cost bound
in an explicit traversal/comparison model. Costs of the entire constructor and
primitive bit operations have **not yet been composed or verified**;
[COST_MODEL.md](COST_MODEL.md) specifies the boundary.

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
python3 scripts/check_executable.py
lake env lean --run WorkChecks.lean
python3 scripts/regenerate_quotient_certificates.py --check
python3 scripts/run_bounded_width_hom_checks.py
```

The Lean audit rejects proof admissions and nonstandard axiom dependencies.
The gadget certificate is evaluated by Lean's kernel; it does not use
`native_decide`. The Python checks independently exercise the executable
construction, but finite tests are not proofs of the general reduction.
Recorded reports are in [sources](sources/).

## Run the verified constructor

```sh
# Summary counts for requested length 1 and the single word 0:
lake env lean --run ReduceLCS.lean 1 0
# Export both graphs as JSON with integer endpoints:
lake env lean --run ReduceLCS.lean --json 1 0 1
```

`LENGTH` is a nonnegative decimal integer. Subsequent arguments are binary words;
use `""` for an empty word and no word arguments for zero words. Raw outputs list
both orientations of each undirected edge. The fixed no-instance uses one edge;
the interpretation of every edge list is undirected. This is a reduction
constructor, not a graph-homomorphism solver. The implementation favors a clear
proof over speed and produces thousands of vertices even for tiny raw inputs.

## Provenance

Extracted from a3nm-032 in `../open-problems`; written proof dated 2026-10-25,
Lean development begun 2026-11-12. Developed with AI assistance; independent
review remains pending. Binary LCS hardness is due to Pietrzak. The direction
gadget is credited to Hell–Nešetřil via Eleftheriadis. See the citations in
[SOLUTION.md](SOLUTION.md). This is separate from the minimum-edge treewidth
problem.
