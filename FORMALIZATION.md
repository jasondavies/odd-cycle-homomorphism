# Formalisation boundary

The Lean development is a **partial formalisation of the written reduction**.
There is no Lean theorem asserting W[1]-hardness or the equivalence of the two
final graph-homomorphism and LCS instances. The results below are fully proved
under their displayed hypotheses, without admissions or project-defined axioms.

## Checked components

| File | Principal result | Meaning |
| --- | --- | --- |
| [PaddedSteps.lean](TreewidthHom/PaddedSteps.lean) | `paddedAdvance_iff` | N steps that stay or advance by one, followed by a strict advance, connect a to b exactly when `a < b ≤ a+N+1`. |
| [LCS.lean](TreewidthHom/LCS.lean) | `commonSubsequence_iff_paddedSelection` | Standard `List.Sublist` common subsequences of length ℓ are equivalent to shared letters and the padded position constraints, when every input length is at most N. |
| [PrimeCycles.lean](TreewidthHom/PrimeCycles.lean) | `cycleHom_dvd`, `prime_cycleHom_eq`, `cycleHom_rotation` | A successor-preserving map on cyclic groups forces divisibility of cycle lengths; prime lengths coincide, and equal nonzero lengths permit only rotations. The actual 18 marker primes are also checked. |
| [ArrowSearch.lean](TreewidthHom/ArrowSearch.lean) | `rigid_hom` | Every mathlib graph endomorphism of the concrete 13-vertex gadget is the identity. |
| [TreeDecomposition.lean](TreewidthHom/TreeDecomposition.lean) | `addApices`, `two_apex_width` | Adding arbitrary edges incident with at most two new vertices preserves a tree-decomposition certificate after adding those vertices to every bag, increasing width by at most two. |

The LCS theorem includes zero length and empty words. Its intermediate statement
is about position constraints, not a definition of the full relational instance.
Identifying those constraints with all Root, Next, Begin, Step, Advance, and
Letter facts remains a separate obligation.

The cycle results use `ZMod` and successor preservation. They do not assert
that a map between the complete cycle-decorated incidence graphs maps each
attached cycle into a single component or sends its root to a root. Those
arguments use the acyclic base and cross-type incidence edges in the prose proof.

The tree-decomposition definition uses mathlib `SimpleGraph.IsTree` and walks.
It requires coverage of vertices and edges and a connected set of occurrence
bags for each vertex. Bags are finite. A width bound is expressed by bounding
every bag's cardinality by width plus one; we have not defined a separate
minimization-based graph treewidth function.

## Finite rigidity certificate

Vertices are numbered in the order
`B,A,x,z,y,D,C,t,a,u,b,v,w`; ports a,b are 8,10. The graph has exactly the edges
of the subdivided K₄ in the written solution. This numbering differs from the
Python implementation and is chosen to prune the search early.

`assignments_complete` proves that **every** edge-preserving bounded map appears
in the backtracking enumeration. The concrete 13-level search is then evaluated
in Lean's kernel and contains only the identity. Concrete intermediate lists
are computation checkpoints, not axioms: each checkpoint's equality with the
preceding search step is kernel-checked. Finally `rigid_hom` applies completeness
to arbitrary mathlib homomorphisms of the gadget.

This certifies all endomorphisms of this one graph. It does **not** certify the
separate confinement theorem for maps into arbitrary graphs formed by gluing
copies of the gadget. Finite Python tests of glued graphs do not replace that
missing general Lean proof.

## Remaining obligations for the complete reduction

1. Define the full relational source and target, and prove their homomorphism
   equivalence with the formalised LCS position constraints.
2. Define typed incidence digraphs and prove both directions of the structural
   homomorphism correspondence.
3. Formalise prime-cycle attachment, component confinement, and root forcing.
4. Formalise the gadget's cycle and port-path properties, arbitrary gluing,
   confinement to one copy, and preservation of the ordered ports.
5. Construct all source and target decompositions, including the pathwidth
   bound `k+1`, incidence and cycle attachments, and gadget attachment bound 12.
6. Compose the constructions; handle the trivial yes/no input cases; prove
   size and running-time bounds, and parameterized-reduction correctness.
7. Supply a formal complexity framework and a formalised or explicitly external
   binary-LCS W[1]-hardness theorem (Pietrzak).

These obligations are not smuggled into Lean as assumed axioms or as a theorem
hypothesis saying that the desired reduction already exists. The current
library simply stops before them. The complete mathematical argument and the
external theorem citations are in [SOLUTION.md](SOLUTION.md).

## Reproduction and trust

Run `python3 scripts/check_formalization.py`. It builds the library and audits
[AxiomAudit.lean](AxiomAudit.lean), allowing only `propext`, `Classical.choice`,
and `Quot.sound`. It also scans the project modules for proof admissions.
The gadget's computation uses `decide +kernel`, not `native_decide`.

The toolchain and mathlib revision are pinned. The audit report is saved as
[sources/lean-verification.json](sources/lean-verification.json). Separately,
`python3 scripts/run_bounded_width_hom_checks.py` verifies finite instances of
the executable reduction and writes
[sources/bounded-width-hom-results.json](sources/bounded-width-hom-results.json).
