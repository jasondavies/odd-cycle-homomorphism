# Formalization boundary

The library checks the finite List Coloring reduction to ordinary homomorphism
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
| Adjacent-bag specialization for paths | `Decomposition.hom_iff_pathBagAssignments`, [BagHomomorphism](TreewidthHom/BagHomomorphism.lean) |

Names abbreviated by `ListReduction` above are under `TreewidthHom.OddCycle`;
other infrastructure is under `TreewidthHom`.

`HasWidth` and `HasPathWidth` are decomposition certificates with checked vertex
coverage, edge coverage, connected occurrences, and bag-size bounds. They are
not oracle assumptions about graph widths. The feedback theorem accepts an
arbitrary set `S` together with acyclicity of `F-S`; it does not require the
caller to supply an orientation. The orientation is derived within Lean.

The finite source graph uses one reference copy for *every* vertex/residue pair,
including allowed colors. A domain link exists only for forbidden colors.
Each original edge is represented once, using increasing vertex indices.
The executable constructor follows the same graph up to vertex renaming.

## Outside Lean

The following are not formalized as machine-level theorems:

- the published complexity of List Coloring;
- the logspace transducer and the polynomial number of output bags;
- time and space analysis of the XNLP and XALP membership algorithms;
- the resulting complexity-class hardness and completeness statements;
- the source's 2-degeneracy and girth.

The paper provides proofs or primary citations for these claims. Noncomputable
choices of roots and owning bags in structural proofs are not verified code for
the logspace transducer. Completeness is stated only with a supplied decomposition.
No W[3]-membership result for feedback vertex number is claimed.

## Reproduction and audits

```sh
python3 scripts/check_formalization.py
python3 scripts/run_list_cycle_checks.py
```

The first command builds the library and audits the 37 declarations listed in
[AxiomAudit.lean](AxiomAudit.lean). It rejects proof admissions and axioms outside
`propext`, `Classical.choice`, and `Quot.sound`. Its report is
[sources/lean-verification.json](sources/lean-verification.json).

The second command checks 837 explicit finite instances, including empty graphs,
empty lists, exhaustive small instances, and seeded instances with path and
branching tree decompositions. It checks satisfiability equivalence, returned
homomorphisms, source size, decompositions, feedback sets and 2-degeneracy.
The direct executable path sweep meets `p+5`; Lean's modular proof uses `p+6`.
See [sources/list-cycle-results.json](sources/list-cycle-results.json).
