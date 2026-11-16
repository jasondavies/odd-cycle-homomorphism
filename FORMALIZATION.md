# Formalisation boundary

The **two combinatorial reductions are checked** in Lean. The hardness of the
starting problems, the resource bounds of the reductions, and the complexity
conclusions are not formal theorems. These are distinct claims.

## Checked statements

The target of both reductions is mathlib's `SimpleGraph.cycleGraph n` for an
odd `n`. Width means a tree-decomposition certificate (`HasWidth`), and a path
decomposition means `HasPathWidth`; both are described below.

**Plain reduction.** For every graph `Γ` on `Fin k × Fin N`,
[`OddCycle.reduction_cycleGraph`](TreewidthHom/OddCycleReduction.lean) proves:

- `Nonempty (source Γ →g cycleGraph n)` if and only if `Γ` has a clique with one
  vertex in each of the `k` classes (`MulticolouredClique`);
- the source has width at most `k+2` and the cycle has width at most `2`;
- deleting `k+1` vertices of the source leaves an acyclic graph
  (`source_feedback`);
- the source has a path decomposition of width at most `k+3`, and the cycle one
  of width at most `2` ([`OddCycle.reduction_pathWidth`](TreewidthHom/OddCyclePathWidth.lean));
- `n` is odd, and the source has at most `(k+1)^2 * n^2` vertices, where
  `n = cycleLength k N = 2*(N*(2*N*k+1+k)+2)+1`.

**Chained reduction.** For every graph `Γ` on `Fin K × Fin N` and layer size
`k > 0`, [`OddCycle.Chained.reduction`](TreewidthHom/OddCycleChained.lean) proves:

- `Nonempty (source k Γ →g cycleGraph n)` if and only if there is one vertex per
  slot such that slots `i < j` with `j/k ≤ i/k + 1` receive adjacent vertices
  (`ChainedClique`). With `K = r*k` this is Chained Multicoloured Clique with
  `r` layers and `k` colours, slot `(t,c)` being numbered `t*k+c`;
- the source has width at most `2k+3`, independently of `K`, and the cycle has
  width at most `2`;
- the source has a path decomposition of width at most `2k+4`, independently
  of `K` ([`OddCycle.Chained.reduction_pathWidth`](TreewidthHom/OddCyclePathWidth.lean));
- `n = cycleLength K N` is odd, and the source has at most `2*(K+1)^2 * n^2`
  vertices.

Both statements hold for all values of the parameters, including zero classes
and empty classes. They depend only on `propext`, `Classical.choice` and
`Quot.sound`.

## File map

| File | Principal result | Meaning |
| --- | --- | --- |
| [OddCycleTarget.lean](TreewidthHom/OddCycleTarget.lean) | `dial`, `walk_iff_ne`, `cyc_eq_cycleGraph` | A map of an odd cycle to itself is a rotation or reflection. Two residues are joined by a walk of length `n-2` exactly when they differ. |
| [Links.lean](TreewidthHom/Links.lean) | `linked_hom_iff` | Homomorphisms out of a graph with attached paths. |
| [OddCycleReduction.lean](TreewidthHom/OddCycleReduction.lean) | `label_solve`, `source_hom_iff_clique`, `source_width`, `target_width`, `reduction_cycleGraph` | Label arithmetic and the plain reduction. |
| [OddCycleChained.lean](TreewidthHom/OddCycleChained.lean) | `Chained.source_hom_iff_clique`, `Chained.source_width`, `Chained.reduction` | The chained reduction. |
| [TreeDecomposition.lean](TreewidthHom/TreeDecomposition.lean), [Width.lean](TreewidthHom/Width.lean) | `Decomposition`, `HasWidth` | Tree-decomposition certificates. |
| [DecompositionMaps.lean](TreewidthHom/DecompositionMaps.lean), [IntervalDecomposition.lean](TreewidthHom/IntervalDecomposition.lean) | `mapEquiv`, `intervalDecomposition` | Relabelling, and decompositions over a path of bags. |
| [GraftTree.lean](TreewidthHom/GraftTree.lean), [GraftDecomposition.lean](TreewidthHom/GraftDecomposition.lean) | `Graft.isTree`, `Graft.running_of_tops`, `Graft.extend` | Grafting trees of bags by parent pointers, with a local criterion for connected occurrences. |
| [BagHomomorphism.lean](TreewidthHom/BagHomomorphism.lean) | `hom_iff_bagAssignments`, `hom_iff_pathBagAssignments`, `two_bag_records_le` | A homomorphism exists exactly when there are assignments on the bags that preserve the edges inside each bag and agree on neighbouring bags. This is the correctness of the membership algorithm in [XNLP_COMPLETENESS.md](XNLP_COMPLETENESS.md), not a machine model of it. |
| [ApexForest.lean](TreewidthHom/ApexForest.lean) | `hasWidth_of_apex_forest`, `acyclic_of_apex_forest`, `hasWidth_of_phased_forest` | Width from a few hubs plus a forest, acyclicity after deleting the hubs, and width from boundedly many retained vertices per phase along a path. |
| [PathWidth.lean](TreewidthHom/PathWidth.lean) | `HasPathWidth`, `hasPathWidth_linked` | Path-decomposition certificates, and a path decomposition for a graph with attached paths swept one at a time. |
| [OddCyclePathWidth.lean](TreewidthHom/OddCyclePathWidth.lean) | `target_pathWidth`, `source_pathWidth`, `Chained.source_pathWidth`, `reduction_pathWidth`, `Chained.reduction_pathWidth` | Pathwidth 2 for the cycle, `k+3` for the plain source and `2k+4` for the chained source. |

## The width notions

`Decomposition G T` uses mathlib trees and walks. It requires vertex coverage,
edge coverage and, for every vertex, a walk between any two of its bags that
stays inside its bags. `HasWidth G w` packages such a certificate with every
bag of size at most `w+1`. `HasPathWidth G w` is the same with the bags arranged
along mathlib's `pathGraph`; it implies `HasWidth G w`. Minimisation-based
treewidth and pathwidth functions are not defined: the theorems exhibit
decompositions.

## Outside Lean

Three things remain outside Lean. They share one cause: each is a statement
about computation or about complexity classes, and neither mathlib nor this
repository has a formal model of space-bounded computation or definitions of
W[1] and XNLP.

1. **Hardness of the starting problems.** W[1]-hardness of Multicoloured
   Clique, and XNLP-completeness of Chained Multicoloured Clique (Bodlaender,
   Groenland, Nederlof, Swennenhuis, Theorem 11), are external published
   inputs, not project axioms. Formalising them means formalising those
   papers' proofs on top of formal definitions of the classes.
2. **Resources of the reductions.** That they run in polynomial time, and in
   logarithmic space as XNLP-hardness requires, is argued in prose. Lean proves
   polynomial bounds on the number of source vertices only. A proof needs a
   machine model with a work-tape space measure and the reduction programmed
   in it.
3. **Membership in XNLP** with a supplied path decomposition, and hence
   XNLP-completeness, is a prose argument in
   [XNLP_COMPLETENESS.md](XNLP_COMPLETENESS.md). Lean checks the combinatorial
   lemma behind it (`hom_iff_pathBagAssignments`), not the time and space
   bounds of the algorithm. A proof needs a nondeterministic machine model
   with simultaneous time and space bounds.

Consequently the complexity conclusions themselves (W[1]-hardness,
W[t]-hardness for every t, XNLP-hardness and XNLP-completeness) are not Lean
theorems. What Lean does establish is every combinatorial fact those
conclusions rest on: correctness of both reductions, their width and size
bounds, and the gluing lemma for membership.

## Reproduction and trust

Run `python3 scripts/check_formalization.py`. It builds the library, audits the
principal declarations listed in [AxiomAudit.lean](AxiomAudit.lean), allowing
only `propext`, `Classical.choice` and `Quot.sound`, and scans the project
modules for proof admissions. The pinned versions and the audit report are
recorded in [sources/lean-verification.json](sources/lean-verification.json).
