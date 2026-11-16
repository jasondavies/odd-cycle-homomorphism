# Formalisation boundary

The **two combinatorial reductions are checked** in Lean. The hardness of the
starting problems, the resource bounds of the reductions, and the complexity
conclusions are not formal theorems. These are distinct claims.

## Checked statements

The target of both reductions is mathlib's `SimpleGraph.cycleGraph n` for an
odd `n`. Width means a tree-decomposition certificate (`HasWidth`, below).

**Plain reduction.** For every graph `Γ` on `Fin k × Fin N`,
[`OddCycle.reduction_cycleGraph`](TreewidthHom/OddCycleReduction.lean) proves:

- `Nonempty (source Γ →g cycleGraph n)` if and only if `Γ` has a clique with one
  vertex in each of the `k` classes (`MulticolouredClique`);
- the source has width at most `k+2` and the cycle has width at most `2`;
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
| [ApexForest.lean](TreewidthHom/ApexForest.lean) | `hasWidth_of_apex_forest`, `hasWidth_of_phased_forest` | Width from a few hubs plus a forest, and from boundedly many retained vertices per phase along a path. |

## The width notion

`Decomposition G T` uses mathlib trees and walks. It requires vertex coverage,
edge coverage and, for every vertex, a walk between any two of its bags that
stays inside its bags. `HasWidth G w` packages such a certificate with every
bag of size at most `w+1`. A minimisation-based treewidth function is not
defined, and there is no separate notion of path decomposition: Lean states
treewidth bounds only.

## Outside Lean

1. **Hardness of the starting problems.** W[1]-hardness of Multicoloured
   Clique, and XNLP-completeness of Chained Multicoloured Clique (Bodlaender,
   Groenland, Nederlof, Swennenhuis), are external published inputs, not
   project axioms.
2. **Resources of the reductions.** That they run in polynomial time, and in
   logarithmic space as XNLP-hardness requires, is argued in prose. Lean proves
   polynomial bounds on the number of source vertices only.
3. **Pathwidth.** The bounds `k+3` and `2k+4`, and the explicit path
   decompositions, are proved in prose. The chained decomposition is checked on
   finite instances by the Python runner.
4. **Membership in XNLP** with a supplied path decomposition, and hence
   XNLP-completeness, is a prose argument in
   [XNLP_COMPLETENESS.md](XNLP_COMPLETENESS.md). Lean checks only the
   combinatorial lemma behind it (`hom_iff_pathBagAssignments`), not the
   time and space bounds.
5. **The complexity conclusions**, since no parameterized-complexity framework
   is formalised.
6. **Feedback vertex number.** The plain width proof deletes exactly the `k+1`
   hubs, but the statement "feedback vertex number at most `k+1`" is not a Lean
   theorem.

## Reproduction and trust

Run `python3 scripts/check_formalization.py`. It builds the library, audits the
principal declarations listed in [AxiomAudit.lean](AxiomAudit.lean), allowing
only `propext`, `Classical.choice` and `Quot.sound`, and scans the project
modules for proof admissions. The pinned versions and the audit report are
recorded in [sources/lean-verification.json](sources/lean-verification.json).
