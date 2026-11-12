# Formalisation boundary

The **complete combinatorial reduction is checked**. The machine-level
polynomial-time reduction and the W[1]-hardness conclusion are not yet formal
complexity theorems. These are distinct claims.

## Main checked statement

For any `words : Fin k → List Bool` and natural requested length `ell`,
[`LCSInstance.full_reduction`](TreewidthHom/FullReduction.lean) proves that
`reduce words ell` is a finite ordinary simple graph pair `(G,H)` satisfying:

- `Nonempty (G →g H)` if and only if there is a list of length `ell` that is a
  `List.Sublist` of every input word (the standard common-subsequence definition).
- `G` has a tree-decomposition certificate of width at most `max(2k,12)`.
- `H` has a tree-decomposition certificate of width at most `12`.
- Each graph has at most `10^12 * (s+1)^12` vertices, where
  `s = k + sum_i length(words i) + 1`.

The size bound is deliberately coarse. It is independent of the requested
length, so it also handles a huge binary-encoded length. Preprocessing maps
zero words or zero requested length to a fixed yes-instance, and any requested
length exceeding an input word's length to a fixed no-instance. All remaining
inputs use the actual padded-path, incidence, prime-cycle, and direction-gadget
construction with padding bound `N = sum_i length(words i)`.
Preprocessing examines lengths only; it does not invoke an LCS solver.

There are no unproved reduction contracts in this statement. It refers to the
actual constructed graph types and mathlib graph homomorphisms. The proof has
only the standard Lean/mathlib dependencies `propext`, `Classical.choice`, and
`Quot.sound`; Pietrzak's theorem is not used or assumed in this combinatorial
statement.

## Checked components

| File | Principal result | Meaning |
| --- | --- | --- |
| [LCS.lean](TreewidthHom/LCS.lean) | `commonSubsequence_iff_embedding` | Standard list subsequences equal shared letters selected by increasing position embeddings. |
| [LCSInstance.lean](TreewidthHom/LCSInstance.lean) | `query`, `target` | The concrete anchored one-unary/five-binary relational construction. |
| [LCSEncode.lean](TreewidthHom/LCSEncode.lean), [LCSDecode.lean](TreewidthHom/LCSDecode.lean) | `commonSubsequence_hom`, `Decode.commonSubsequence` | Both directions of the relational front end. |
| [LCSReduction.lean](TreewidthHom/LCSReduction.lean) | `lcs_graph_iff` | Decision equivalence for the actual final simple graphs, including zero words and empty subsequences. |
| [LCSQueryWidth.lean](TreewidthHom/LCSQueryWidth.lean) | `query_width` | Source path-decomposition bags have size at most `2k+1`. |
| [LCSTargetWidth.lean](TreewidthHom/LCSTargetWidth.lean) | `target_width` | Target Gaifman bags have size at most five. |
| [Incidence.lean](TreewidthHom/Incidence.lean), [IncidenceWidth.lean](TreewidthHom/IncidenceWidth.lean) | `incidence_iff`, `incidence_width` | Typed incidence preserves homomorphisms; unary/binary facts extend width to at most `max(w,4)`. |
| [ColorEncoding.lean](TreewidthHom/ColorEncoding.lean), [ColorWidth.lean](TreewidthHom/ColorWidth.lean) | `colorEncoding_iff`, `colorEncoding_width` | Prime-cycle type erasure preserves homomorphisms and extends width to at most `max(w,2)`. |
| [ArrowConfinement.lean](TreewidthHom/ArrowConfinement.lean) | `Assembly.confinement` | Every gadget map into an arbitrary assembly is the coordinate-preserving inclusion of one copy. |
| [DirectionReduction.lean](TreewidthHom/DirectionReduction.lean), [DirectionWidth.lean](TreewidthHom/DirectionWidth.lean) | `directionReduction_iff`, `directionReduction_width` | Direction erasure preserves homomorphisms and extends width to at most `max(w,12)`; exact count is `|V|+11|E|`. |
| [Schema.lean](TreewidthHom/Schema.lean) | `schema_tags_card`, `standardMarkers_bound` | The 18 incidence types use distinct primes at most 67. |
| [ReductionWidth.lean](TreewidthHom/ReductionWidth.lean) | `lcs_bounded_graph_reduction` | Composed correctness with final source and target width certificates. |
| [FiniteEncoding.lean](TreewidthHom/FiniteEncoding.lean), [ReductionSize.lean](TreewidthHom/ReductionSize.lean) | `schema_graph_card_le`, `graph_bound_of_domain` | Finite graph types and polynomial vertex counts. |
| [FullReduction.lean](TreewidthHom/FullReduction.lean) | `full_reduction` | All input cases, decision equivalence, widths, and polynomial size in one theorem. |

Reusable infrastructure includes arbitrary leaf attachment (`LeafTree`,
`LeafExtension`), well-founded tree grafting (`GraftTree`), fan decompositions
(`ConeDecomposition`, `ChainGraft`), relabeling and edge deletion
(`DecompositionMaps`), and interval/path decompositions (`IntervalDecomposition`).
The earlier `PaddedSteps` and `PrimeCycles` lemmas remain checked as well.

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

## Remaining complexity obligations

The combinatorial reduction has no remaining correctness, width, finiteness,
or polynomial-output-size assumptions. The following are outside the current
formal theorem:

1. Implement and verify an encoded constructor in a machine or bit-cost model,
   and prove its polynomial running time. The Lean graph definitions use
   noncomputable finite enumerations; the separately tested Python program is
   not formally proved to implement them. Polynomial output size by itself is
   not a running-time proof.
2. Instantiate a formal parameterized-reduction framework and derive the
   W[1]-hardness conclusion. Pietrzak's binary-LCS hardness theorem remains an
   explicitly external published input, not a project axiom.
3. Optionally sharpen the checked source bound from `2k` to the written `k+1`,
   the intermediate target bound from four to three, and the coarse size bound
   to the written sparse quadratic bound. None of these improvements changes
   the intended parameterized-hardness conclusion or final target width 12.

The tree-decomposition certificates use mathlib trees and walks, require vertex
and edge coverage and connected occurrence bags, and bound every finite bag by
width plus one. `HasWidth` packages such a certificate; a minimization-based
graph treewidth function is not defined. Existence of a decidable-equality
instance in this package is bookkeeping for finite sets, not a graph assumption.

## Reproduction and trust

Run `python3 scripts/check_formalization.py`. It builds the library and audits
54 principal declarations in
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
