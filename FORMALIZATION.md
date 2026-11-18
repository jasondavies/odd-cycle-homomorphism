# Formalisation boundary

The library checks the finite List Colouring reduction to ordinary homomorphism
into an odd cycle. The principal declaration is
[`TreewidthHom.OddCycle.ListReduction.reduction`](TreewidthHom/ListTheorem.lean),
which transfers decomposition certificates.
[`ListReduction.parameter_reduction`](TreewidthHom/Parameters.lean) restates it
as inequalities between treewidth, pathwidth and feedback vertex number, and adds
the sparsity of the source.
The target `OddCycle.cyc n` is mathlib's `circulantGraph {1}` on `ZMod n`.
`OddCycle.cyc_eq_cycleGraph` identifies it with mathlib's `cycleGraph` for
successor lengths. No source or target lists remain in the output problem.

## Checked statements

| Statement | Declaration / module |
| --- | --- |
| Odd-cycle endomorphisms are rotations or reflections | `OddCycle.rotation_or_reflection`, [OddCycleTarget](TreewidthHom/OddCycleTarget.lean) |
| Length-`n-2` links enforce distinct images | `OddCycle.walk_iff_ne`, [OddCycleTarget](TreewidthHom/OddCycleTarget.lean) |
| Odd closed walks in `C_n` have length at least `n` | `OddCycle.odd_closed_walk_length`, [OddCycleTarget](TreewidthHom/OddCycleTarget.lean) |
| Odd-cycle homomorphisms cannot increase length; equivalence forces equal lengths | `OddCycle.length_le_of_hom`, `OddCycle.length_eq_of_homs`, [OddCycleTarget](TreewidthHom/OddCycleTarget.lean) |
| Endpoints of every odd-length subdivision walk project to adjacent colours | `OddCycle.subdivisionProjection_walk`, [OddSubdivision](TreewidthHom/OddSubdivision.lean) |
| Reachable endpoint differences form a cyclic interval after multiplication by the inverse of two | `OddCycle.walk_iff_interval`, [CycleWalkInterval](TreewidthHom/CycleWalkInterval.lean) |
| Lists contained in a smaller palette omit coordinate `n-1` | `ListReduction.palette_missing_last`, [ListReduction](TreewidthHom/ListReduction.lean) |
| Fixed selector images extend to a colouring iff the formula is true on those variables | `WeightedFormula.Formula.extends_iff`, [WeightedFormula](TreewidthHom/WeightedFormula.lean) |
| Removing the selectors leaves a tree; exact-weight satisfiability reduces to both graph problems with a feedback set of size `k+2` | `selectors_tree`, `satisfiable_iff_colorable`, `cycle_reduction`, [WeightedCycle](TreewidthHom/WeightedCycle.lean) |
| Girth `n` and order at most `4*n^3` for nonempty inputs with `m ≤ n` | `ListReduction.source_girth_and_card`, [Parameters](TreewidthHom/Parameters.lean) |
| Decision equivalence | `ListReduction.source_hom_iff_colorable`, [ListReduction](TreewidthHom/ListReduction.lean) |
| Rooted-tree attachments give width at most `max(w,1)` | `Graft.hasWidth`, [GraftWidth](TreewidthHom/GraftWidth.lean) |
| Source treewidth `max(w+2,3)` | `ListReduction.source_width`, [ListWidth](TreewidthHom/ListWidth.lean) |
| Source pathwidth `p+6` | `ListReduction.source_pathWidth`, [ListPathWidth](TreewidthHom/ListPathWidth.lean) |
| Finite-index tree certificates give the same width on finite graphs | `hasFiniteWidth_iff_hasWidth`, `finite_decomposition_at_treewidth`, [FiniteDecomposition](TreewidthHom/FiniteDecomposition.lean) |
| Polynomial output tree and path bag counts from supplied certificates | `ListReduction.source_tree_bag_bound`, `source_path_certificate`, [ListCertificates](TreewidthHom/ListCertificates.lean) |
| Target pathwidth 2 | `OddCycle.target_pathWidth`, [CycleWidth](TreewidthHom/CycleWidth.lean) |
| Forest orientation exists | `exists_forestOrientation`, [ForestOrientation](TreewidthHom/ForestOrientation.lean) |
| Transferred set leaves an acyclic graph | `ListReduction.source_feedback`, [ListFeedback](TreewidthHom/ListFeedback.lean) |
| Transferred set has cardinality `S.card+2` | `ListReduction.removed_card`, [ListFeedback](TreewidthHom/ListFeedback.lean) |
| Polynomial source cardinality | `ListReduction.source_card_le`, [ListTheorem](TreewidthHom/ListTheorem.lean) |
| Combined certificate | `ListReduction.reduction`, [ListTheorem](TreewidthHom/ListTheorem.lean) |
| Treewidth, pathwidth and feedback vertex number as minima, attained for finite graphs | `treewidth`, `pathwidth`, `fvs`, `hasWidth_treewidth`, `hasPathWidth_pathwidth`, `exists_fvs`, [Parameters](TreewidthHom/Parameters.lean) |
| `tw(G) ≤ max(tw(F)+2,3)`, `pw(G) ≤ pw(F)+6`, `fvs(G) ≤ fvs(F)+2` | `ListReduction.treewidth_source_le`, `pathwidth_source_le`, `fvs_source_le`, [Parameters](TreewidthHom/Parameters.lean) |
| Source is 2-degenerate | `ListReduction.source_degenerate`, [ListSparse](TreewidthHom/ListSparse.lean) |
| Every source cycle has length at least `n`; girth exactly `n` for nonempty `F` | `ListReduction.source_cycle_length`, `source_egirth`, [ListSparse](TreewidthHom/ListSparse.lean) |
| Source is connected when every list omits a residue | `ListReduction.source_connected`, [ListSparse](TreewidthHom/ListSparse.lean) |
| A `k`-degenerate graph has at most `k|V|` edges; the source has at most `2|V|` | `IsDegenerate.card_edgeSet_le`, `ListReduction.source_edges_le`, [ListSparse](TreewidthHom/ListSparse.lean), [Parameters](TreewidthHom/Parameters.lean) |
| Parameter form of the reduction with sparsity | `ListReduction.parameter_reduction`, [Parameters](TreewidthHom/Parameters.lean) |
| Consistent local assignments glue to a homomorphism | `Decomposition.hom_iff_bagAssignments`, [BagHomomorphism](TreewidthHom/BagHomomorphism.lean) |
| Adjacent-bag specialisation for paths | `Decomposition.hom_iff_pathBagAssignments`, [BagHomomorphism](TreewidthHom/BagHomomorphism.lean) |
| A guess on a feedback vertex set extends exactly when it preserves edges inside the set and every root of the remaining forest has a feasible pair | `Feedback.extends_iff`, `Feedback.feasible_iff`, [FeedbackHomomorphism](TreewidthHom/FeedbackHomomorphism.lean) |
| Join minor under a common forbidden last coordinate | `ListReduction.join_minor`, [ListMinor](TreewidthHom/ListMinor.lean) |
| Minor monotonicity of treewidth, pathwidth and feedback vertex number | `MinorModel.treewidth_le`, `pathwidth_le`, `fvs_le`, [MinorModel](TreewidthHom/MinorModel.lean) |
| Exact treewidth and pathwidth increases on joining a clique | `treewidth_apexJoin`, `pathwidth_apexJoin`, [JoinWidth](TreewidthHom/JoinWidth.lean) |
| Exact treewidth and feedback-number transfer; pathwidth lower bound | `ListReduction.exact_parameter_transfer`, `source_width_lower`, [ListExact](TreewidthHom/ListExact.lean) |
| Target capping and bipartiteness for oversized targets | `OddCycle.hom_iff_capped`, `hom_iff_bipartite_of_card_lt`, [BinaryTarget](TreewidthHom/BinaryTarget.lean) |
| Odd closed walks contain odd cycles; finite odd girth is attained | `OddCycle.odd_cycle_of_odd_closed_walk`, `exists_oddGirth_eq_length`, [OddGirth](TreewidthHom/OddGirth.lean) |
| Odd cycles are cores; recognition iff mapping to a shortest odd cycle | `OddCycle.cycle_isCore`, `hasOddCycleCore_iff_of_oddGirth`, [OddCycleCore](TreewidthHom/OddCycleCore.lean) |
| Target-free finite reduction | `ListReduction.source_hasOddCycleCore_iff`, [OddCycleCore](TreewidthHom/OddCycleCore.lean) |

Names abbreviated by `ListReduction` above are under `TreewidthHom.OddCycle`;
other infrastructure is under `TreewidthHom`.

`HasWidth` and `HasPathWidth` are decomposition certificates with checked vertex
coverage, edge coverage, connected occurrences, and bag-size bounds. They are
not oracle assumptions about graph widths. The feedback theorem accepts an
arbitrary set `S` together with acyclicity of `F-S`; it does not require the
caller to supply an orientation. The orientation is derived within Lean.

`HasFiniteWidth` requires a bag tree indexed by `Fin N`. The library proves
that this has the same meaning as `HasWidth` on finite graphs, including the
empty graph. It selects finitely many covering bags, connects them inside the
original tree, restricts the decomposition, and relabels the finite subtree.
This existence proof does not bound the size of that subtree.

Separately, `HasWidthWithBags` and `HasPathWidthWithBags` record an upper bound
on the number of supplied bags. From a certificate with at most `N` bags for an
`m`-vertex input and target length `n`, the construction gives at most

- `N + m*n*n + (m*n+m*m)*n` tree bags, of width `max(w+2,3)`;
- `N*(2*(m*n*n+2))*((m*n+m*m+1)*n)` path bags, of width `p+6`.

These are checked cardinality bounds for finite certificates, polynomial in
`m,n,N`. They do not assert an encoded transducer or its workspace bound.

`treewidth`, `pathwidth` and `fvs` are infima over these certificates. For a
finite graph the infimum is attained, which the transfer inequalities use for
the input graph. `IsDegenerate G k` says that every nonempty finite vertex set
contains a vertex with at most `k` neighbours in the set. Girth is mathlib's
`egirth`.

`Feedback.extends_iff` is the correctness argument for the W[P] membership
algorithm: guess images for a feedback vertex set, then evaluate the
feasibility recurrence `Feedback.feasible_iff` on the remaining forest from the
leaves upwards. It does not assert machine resource bounds.

The finite source graph uses one reference copy for *every* vertex/residue pair,
including allowed colours. A domain link exists only for forbidden colours.
Each original edge is represented once, using increasing vertex indices.
The executable constructor follows the same graph up to vertex renaming.
The sharper treewidth upper bound holds even for full lists. The exact
parameter equalities in the paper use a forbidden private coordinate at every
hub and an input edge. They are checked by `exact_parameter_transfer` under
those explicit hypotheses; the generic upper-bound theorem remains applicable
to full lists. The pathwidth lower bound requires only nonempty input.

The new minor model uses disjoint, nonempty connected branch sets with an edge
witness for each minor edge. Its decomposition transfer and feedback-set
projection prove minor monotonicity. `TreeHelly` proves the finite Helly property
for subtrees, giving the join's exact treewidth and pathwidth increases.
`OddCycle.oddGirth` is the infimum of the lengths
of odd cycles, with infinity when none exists. Odd cycles are proved to satisfy
the finite-core endomorphism criterion. Recognition is stated as existence of
homomorphisms in both directions with an odd cycle; no algorithm for constructing
a canonical core is asserted.

## Outside Lean

Finite tree-certificate representation and polynomial output bag counts are
checked. The remaining representation work concerns bit-level encodings and
palette compaction: the vertex and bag bounds are polynomial in numeric
parameters, and their connection to encoded input length remains textual.

The following also remain outside the formalisation:

- the published width hardness of List Colouring and the W[SAT]-completeness of Weighted Antimonotone Satisfiability;
- the logspace transducer and the encoding of its output certificates;
- time and space analysis of the XNLP, XALP and W[P] membership algorithms;
- the resulting complexity-class hardness and completeness statements;
- the implementation and resource bound of the binary-to-unary transducer
  (its target-capping equivalence is checked);
- the algorithm for circular-clique thresholds and the exact circular chromatic
  number, including chain compression and difference constraints;
- the sampled tree-tour algorithm for long target cycles and its odd-girth
  corollary in the [companion note](paper/long-odd-cycles.pdf);
- the circular-chromatic-number interpretation, and the complexity
  classifications for odd-cycle-core recognition (its graph-theoretic equivalence
  and finite reduction are checked).

The manuscripts provide proofs or primary citations for these claims. Noncomputable
choices of roots and owning bags in structural proofs are not verified code for
the logspace transducer. The Python construction is independently tested; no
universal refinement theorem connects its output to the Lean graph. The XNLP
and XALP completeness statements use supplied
decompositions. For feedback vertex number, the W[P] upper bound needs no
supplied decomposition; the paper proves it directly and also derives it from
Binary CSP. The formula gadget supplies the combinatorial part of the W[SAT] lower bound.

## Independent Palomar statement

[`TreewidthHom.Palomar.list_elimination`](Solution.lean) packages the finite
reduction and sparse-source properties as one existential theorem, choosing the
existing concrete construction as its witness. [Challenge.lean](Challenge.lean)
repeats its mathematical definitions and statement using only Mathlib imports.
The deliberately omitted Challenge proof is excluded from the proof-admission
audit; the proved Solution is included. [Comparator](comparator.json) compares
the two independently compiled modules. See [PALOMAR.md](PALOMAR.md) for the
precise scope and reproduction commands.

## Reproduction and audits

See the [README reproduction commands](README.md#reproduce) for setup and execution.

`scripts/check_formalization.py` builds the library and audits the 117 declarations
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

Regression tests additionally validate the join-minor branch sets and exhaustively
check the feedback-number lower bound on an edge and a triangle. They also check
the sharper treewidth certificate on full and empty lists. These finite examples
supplement the universal Lean proof of exactness.
