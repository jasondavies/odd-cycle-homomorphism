# Formalisation boundary

The complete W[1]-hardness theorem is **not yet formalised**. The library now
checks the entire relational-to-simple-graph homomorphism equivalence, including
arbitrary gadget gluing. The remaining gap starts with the LCS relational front
end and includes some width and size bounds.

## Checked components

| File | Principal result | Meaning |
| --- | --- | --- |
| [PaddedSteps.lean](TreewidthHom/PaddedSteps.lean) | `paddedAdvance_iff` | N steps that stay or advance by one, followed by a strict advance, connect a to b exactly when `a < b ≤ a+N+1`. |
| [LCS.lean](TreewidthHom/LCS.lean) | `commonSubsequence_iff_paddedSelection` | Standard list common subsequences are equivalent to the padded position constraints. |
| [Incidence.lean](TreewidthHom/Incidence.lean) | `incidence_iff` | For arbitrary finite-arity relational structures, structural homomorphisms are equivalent to type-preserving incidence homomorphisms. |
| [ColorEncoding.lean](TreewidthHom/ColorEncoding.lean) | `colorEncoding_iff` | Attaching distinct prime cycles to a typed acyclic digraph preserves homomorphism existence after erasing types. |
| [RelationalReduction.lean](TreewidthHom/RelationalReduction.lean) | `relationalReduction_iff` | All three schema-erasure stages compose: relational homomorphisms are equivalent to homomorphisms of the final simple undirected graphs. |
| [Schema.lean](TreewidthHom/Schema.lean) | `schema_tags_card`, `standardMarkers_bound` | The one-unary/five-binary schema has exactly 18 incidence types, instantiated by distinct primes at most 67. |
| [ArrowSearch.lean](TreewidthHom/ArrowSearch.lean) | `rigid_hom` | Every endomorphism of the concrete 13-vertex gadget is the identity. |
| [ArrowConfinement.lean](TreewidthHom/ArrowConfinement.lean) | `Assembly.confinement` | Every map from the gadget into an arbitrary assembly of copies is the coordinate-preserving inclusion of a single copy. |
| [DirectionReduction.lean](TreewidthHom/DirectionReduction.lean) | `directionReduction_iff`, `directionReduction_card` | Direction removal preserves homomorphism existence and has exactly `|V| + 11|E|` vertices. |
| [DirectionWidth.lean](TreewidthHom/DirectionWidth.lean) | `directionReduction_width` | Any width-k decomposition extends to the undirected gadget replacement with width at most `max(k,12)`. |
| [LeafTree.lean](TreewidthHom/LeafTree.lean) | `leafTree.isTree` | Adding arbitrary families of leaves preserves the tree property. |
| [TreeDecomposition.lean](TreewidthHom/TreeDecomposition.lean) | `addApices`, `two_apex_width` | Adding two apices increases a supplied decomposition's width by at most two. |

The theorem `relationalReduction_iff` constructs the actual incidence vertices,
prime-cycle vertices and gadget vertices. Its conclusion concerns mathlib
homomorphisms of ordinary simple graphs; it is not an assumed equivalence or
an abstract contract for an unspecified encoding. Its inputs include a marker
assignment with distinct prime lengths. `schemaMarkers` supplies one for the
fixed six-relation schema used in the written proof.

## General confinement from a finite quotient certificate

Vertices are numbered `B,A,x,z,y,D,C,t,a,u,b,v,w`; ports a,b are 8,10. Collapsing
both ports to 8 gives a finite quotient graph (with unused vertex 10 isolated).
There are exactly eight homomorphisms from the gadget into this quotient.
[ArrowQuotient.lean](TreewidthHom/ArrowQuotient.lean) checks a complete search
and a decreasing-distance certificate for every resulting map. Each certificate
proves that vertex 7 has a non-port image, that all non-port preimages connect
to it, and that every port preimage has a non-port neighbor.

For an arbitrary assembly, collapse all base vertices to 8 and retain private
coordinates. Composing an arbitrary gadget map with this projection gives one
of the certified quotient maps. Adjacent private vertices have the same copy
index, so the decreasing-distance certificate places all private images in a
single copy. Every other image has a private neighbor and belongs to that copy
too. Its inclusion is an induced embedding; the previously proved rigidity
then fixes all coordinates and preserves the ordered ports.

This is a general proof for assemblies of **any size, including infinite ones**.
The assembly may contain parallel directed arcs, but each copy must have
 distinct endpoints. `directionReduction_iff` applies it to loopless digraphs;
only its source needs to have no isolated vertices. Prime-cycle decoration
automatically supplies that property in the composed relational reduction.

The quotient argument provides a checked alternative to the prose solution's
odd-cycle confinement proof. No separate formalisation of that longer proof
is needed for the checked equivalence.

## Prime-cycle confinement

[CycleRank.lean](TreewidthHom/CycleRank.lean) proves that a natural-valued rank
which never decreases around a finite cycle is constant. In the encoded target,
base arcs strictly increase rank, so an image cycle stays in one component.
Its coordinate map preserves successor, and the divisibility theorem from
[PrimeCycles.lean](TreewidthHom/PrimeCycles.lean) forces equal prime types.
A cross-type source arc must therefore map to a cross-component target arc.
Projecting images to their components recovers a typed homomorphism. This even
works for isolated vertices of the original typed graph.

## Remaining obligations

1. Define the full LCS relational source and target, and identify their
   homomorphisms with the already formalised padded-position constraints.
2. Construct their width bounds: source pathwidth at most `k+1` and target
   treewidth at most three.
3. Extend decompositions through incidence and prime-cycle attachment. The
   final direction-removal width bound **is already checked**.
4. Prove all finite size/construction-time bounds and handle the full reduction's
   trivial yes/no input cases. The direction stage's exact vertex count is checked.
5. State the parameterized-reduction conclusion in a complexity framework,
   with Pietrzak's LCS W[1]-hardness theorem kept explicitly external or formalised.

The tree-decomposition certificates use mathlib trees and walks, require vertex
and edge coverage and connected occurrence bags, and bound every finite bag by
width plus one. A minimization-based graph treewidth function is not defined.

## Reproduction and trust

Run `python3 scripts/check_formalization.py`. It builds the library and audits
[AxiomAudit.lean](AxiomAudit.lean), allowing only `propext`, `Classical.choice`,
and `Quot.sound`. It also scans project modules for proof admissions. Both finite
searches use kernel reduction, without `native_decide` or project axioms.

Run `python3 scripts/regenerate_quotient_certificates.py --check` to reproduce
the eight quotient maps and their distance certificates. The generator is
outside the proof's trusted base: Lean checks each generated certificate.

The pinned versions and audit report are recorded in
[sources/lean-verification.json](sources/lean-verification.json). Separate finite
checks of the executable reduction remain in
[sources/bounded-width-hom-results.json](sources/bounded-width-hom-results.json).
