# Formalisation boundary

The library checks the finite List Colouring reduction to ordinary homomorphism
into an odd cycle. The principal declaration is
[`TreewidthHom.OddCycle.ListReduction.reduction`](TreewidthHom/ListTheorem.lean).
The target `OddCycle.cyc n` is mathlib's `circulantGraph {1}` on `ZMod n`.
`OddCycle.cyc_eq_cycleGraph` identifies it with mathlib's `cycleGraph` for
successor lengths. No source or target lists remain in the output problem.

## Checked statements

| Statement | Declaration / module |
| --- | --- |
| Odd-cycle endomorphisms are rotations or reflections | `OddCycle.rotation_or_reflection`, [OddCycleTarget](TreewidthHom/OddCycleTarget.lean) |
| Length-`n-2` links enforce distinct images | `OddCycle.walk_iff_ne`, [OddCycleTarget](TreewidthHom/OddCycleTarget.lean) |
| Decision equivalence | `ListReduction.source_hom_iff_colorable`, [ListReduction](TreewidthHom/ListReduction.lean) |
| Source treewidth `max(w+2,4)` | `ListReduction.source_width`, [ListWidth](TreewidthHom/ListWidth.lean) |
| Source pathwidth `p+6` | `ListReduction.source_pathWidth`, [ListPathWidth](TreewidthHom/ListPathWidth.lean) |
| Target pathwidth 2 | `OddCycle.target_pathWidth`, [CycleWidth](TreewidthHom/CycleWidth.lean) |
| Forest orientation exists | `exists_forestOrientation`, [ForestOrientation](TreewidthHom/ForestOrientation.lean) |
| Transferred set leaves an acyclic graph | `ListReduction.source_feedback`, [ListFeedback](TreewidthHom/ListFeedback.lean) |
| Transferred set has cardinality `S.card+2` | `ListReduction.removed_card`, [ListFeedback](TreewidthHom/ListFeedback.lean) |
| Polynomial source cardinality | `ListReduction.source_card_le`, [ListTheorem](TreewidthHom/ListTheorem.lean) |
| Combined certificate | `ListReduction.reduction`, [ListTheorem](TreewidthHom/ListTheorem.lean) |
| Consistent local assignments glue to a homomorphism | `Decomposition.hom_iff_bagAssignments`, [BagHomomorphism](TreewidthHom/BagHomomorphism.lean) |
| Adjacent-bag specialisation for paths | `Decomposition.hom_iff_pathBagAssignments`, [BagHomomorphism](TreewidthHom/BagHomomorphism.lean) |

Names abbreviated by `ListReduction` above are under `TreewidthHom.OddCycle`;
other infrastructure is under `TreewidthHom`.

`HasWidth` and `HasPathWidth` are decomposition certificates with checked vertex
coverage, edge coverage, connected occurrences, and bag-size bounds. They are
not oracle assumptions about graph widths. The feedback theorem accepts an
arbitrary set `S` together with acyclicity of `F-S`; it does not require the
caller to supply an orientation. The orientation is derived within Lean.

The finite source graph uses one reference copy for *every* vertex/residue pair,
including allowed colours. A domain link exists only for forbidden colours.
Each original edge is represented once, using increasing vertex indices.
The executable constructor follows the same graph up to vertex renaming.

## Outside Lean

The following are not formalised as machine-level theorems:

- the published complexity of List Colouring;
- the logspace transducer and the polynomial number of output bags;
- time and space analysis of the XNLP and XALP membership algorithms;
- the resulting complexity-class hardness and completeness statements;
- the source's 2-degeneracy, girth and connectedness.

The paper provides proofs or primary citations for these claims. Noncomputable
choices of roots and owning bags in structural proofs are not verified code for
the logspace transducer. The XNLP and XALP completeness statements use supplied
decompositions. For feedback vertex number, the W[P] upper bound follows from
Binary CSP and needs no supplied decomposition; no W[3]-membership result is claimed.

## Reproduction and audits

See the [README reproduction commands](README.md#reproduce) for setup and execution.

`scripts/check_formalization.py` builds the library and audits the 37 declarations
listed in [AxiomAudit.lean](AxiomAudit.lean). It rejects proof admissions and axioms outside
`propext`, `Classical.choice`, and `Quot.sound`. Its report is
[reports/lean-verification.json](reports/lean-verification.json). The report
records the project commit and working-tree status sampled before verification.
A dirty report describes a working tree, not just the named commit. All acceptance
checks remain active under `python -O`, `python -OO`, and `PYTHONOPTIMIZE`.

`scripts/run_list_cycle_checks.py` checks 841 explicit finite instances, including
empty graphs, empty lists, exhaustive small instances, and seeded instances with path and
branching tree decompositions. It checks satisfiability equivalence, returned
homomorphisms, source size, decompositions, feedback sets and 2-degeneracy.
Three positive cyclic cases exercise nonempty input feedback sets, including
a branching decomposition. Five targeted cases (including empty input) also check
exact girth independently by breadth-first search.
The direct executable path sweep meets `p+5`; Lean's modular proof uses `p+6`.
See [reports/list-cycle-results.json](reports/list-cycle-results.json).
