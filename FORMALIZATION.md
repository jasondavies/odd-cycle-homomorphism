# Formalisation boundary

The **complete combinatorial reduction is checked**. The machine-level
polynomial-time reduction and the hardness conclusions (W[1] for binary strings;
W[t] for all t and XNLP for arbitrary alphabets) are not yet formal complexity
theorems. These are distinct claims.

## Main checked statement

For any `words : Fin k → List Bool` and natural requested length `ell`,
[`LCSInstance.full_reduction`](TreewidthHom/FullReduction.lean) proves that
`reduce words ell` is a finite ordinary simple graph pair `(G,H)` satisfying:

- `Nonempty (G →g H)` if and only if there is a list of length `ell` that is a
  `List.Sublist` of every input word (the standard common-subsequence definition).
- `G` has a tree-decomposition certificate of width at most `max(2k,3)`.
- `H` has a tree-decomposition certificate of width at most `3`.
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

## Verified executable output

[`Executable.compile_spec`](TreewidthHom/ExecutableReduction.lean) establishes
the same decision, width and size specification for an executable function
`compile : List (List Bool) → Nat → Pair`. Each `Pair` contains two `EdgeList`
records with an order and a list of bounded integer endpoint pairs.

Explicit duplicate-free enumerations replace classical finite-set choices.
The 18 prime markers are assigned in explicit tag-enumeration order; they need
not coincide with the earlier noncomputable assignment. The general marker
correctness and width lemmas apply to this assignment as well. Typed incidence
arcs and marker-cycle arcs are generated directly, with injectivity and
surjectivity proofs. Private gadget vertices use arithmetic offsets, so their
numbering does not search the final vertex list. `indexedAssemblyIso` and
`relationalGraphIso` verify the graph interpretation of the integer encoding.

The Lean compiler accepts all constructor definitions as computable; none is
marked `noncomputable`. Proofs may use the usual standard logical axioms, which
are erased during execution. The CLI in [ReduceLCS.lean](ReduceLCS.lean) exports
this constructor's actual output. Parsing/JSON-library implementation costs are
not part of the graph-construction theorem.

The regression runner checks six graph pairs, including a requested length of
`2^256`, against independent formula counts, and checks endpoint validity,
looplessness, duplicate edges, and raw-output symmetry. General decision
correctness follows from Lean, not these tests. The original Python reduction
is still a separate implementation without a formal refinement theorem.

## Complete abstract cost composition

[`compileMeasured_value`](TreewidthHom/MeasuredReduction.lean) proves that the
complete instrumented constructor returns exactly `compile`'s graph data.
`compileMeasured_polynomial` bounds its cost by a single polynomial in
`100 + encodedInputSize xs ell + q`, with `q` the assigned primitive charge.
Preprocessing, finite relation searches, domain/fact/incidence/marker enumeration,
sparse arcs, and integer serialization are all included. The input size includes
the binary length of the requested subsequence length.

This closes the previous whole-constructor cost-composition obligation in the
stated abstract model. It does not certify primitive bit costs, compile the
program to a machine model, or bound the ordinary Lean CLI's runtime.
[COST_MODEL.md](COST_MODEL.md) describes the charged operations precisely.
`MeasuredChecks.lean` compares the two executable outputs on both preprocessing
branches and full constructions; the general equality is proved in Lean.

## Checked components

| File | Principal result | Meaning |
| --- | --- | --- |
| [LCS.lean](TreewidthHom/LCS.lean) | `commonSubsequence_iff_embedding` | Standard list subsequences equal shared letters selected by increasing position embeddings. |
| [LCSInstance.lean](TreewidthHom/LCSInstance.lean) | `query`, `target` | The concrete anchored one-unary/five-binary relational construction. |
| [LCSEncode.lean](TreewidthHom/LCSEncode.lean), [LCSDecode.lean](TreewidthHom/LCSDecode.lean) | `commonSubsequence_hom`, `Decode.commonSubsequence` | Both directions of the relational front end. |
| [LCSReduction.lean](TreewidthHom/LCSReduction.lean) | `lcs_graph_iff` | Decision equivalence for the actual final simple graphs, including zero words and empty subsequences. |
| [LCSQueryWidth.lean](TreewidthHom/LCSQueryWidth.lean) | `query_width` | Source path-decomposition bags have size at most `2k+1`. |
| [LCSTargetWidth.lean](TreewidthHom/LCSTargetWidth.lean) | `target_width` | Target Gaifman bags have size at most four: a width-one forest decomposition plus the two letter vertices. |
| [Incidence.lean](TreewidthHom/Incidence.lean), [IncidenceWidth.lean](TreewidthHom/IncidenceWidth.lean) | `incidence_iff`, `incidence_width` | Typed incidence preserves homomorphisms; unary/binary facts extend width to at most `max(w,2)`. |
| [ColorEncoding.lean](TreewidthHom/ColorEncoding.lean), [ColorWidth.lean](TreewidthHom/ColorWidth.lean) | `colorEncoding_iff`, `colorEncoding_width` | Prime-cycle type erasure preserves homomorphisms and extends width to at most `max(w,2)`. |
| [ArrowConfinement.lean](TreewidthHom/ArrowConfinement.lean) | `Assembly.confinement` | Every gadget map into an arbitrary assembly is the coordinate-preserving inclusion of one copy. |
| [DirectionReduction.lean](TreewidthHom/DirectionReduction.lean), [DirectionWidth.lean](TreewidthHom/DirectionWidth.lean) | `directionReduction_iff`, `directionReduction_width` | Direction erasure preserves homomorphisms and extends width to at most `max(w,3)`; exact count is `|V|+11|E|`. |
| [Schema.lean](TreewidthHom/Schema.lean) | `schema_tags_card`, `standardMarkers_bound` | The 18 incidence types use distinct primes at most 67. |
| [ReductionWidth.lean](TreewidthHom/ReductionWidth.lean) | `lcs_bounded_graph_reduction` | Composed correctness with final source and target width certificates. |
| [FiniteEncoding.lean](TreewidthHom/FiniteEncoding.lean), [ReductionSize.lean](TreewidthHom/ReductionSize.lean) | `schema_graph_card_le`, `graph_bound_of_domain` | Finite graph types and polynomial vertex counts. |
| [FullReduction.lean](TreewidthHom/FullReduction.lean) | `full_reduction` | All input cases, decision equivalence, widths, and polynomial size in one theorem. |

Reusable infrastructure includes arbitrary leaf attachment (`LeafTree`,
`LeafExtension`), well-founded tree grafting (`GraftTree`), grafted bag trees
with a local connectedness criterion (`GraftDecomposition`), fan decompositions
(`ConeDecomposition`, `ChainGraft`), relabeling and edge deletion
(`DecompositionMaps`), and interval/path decompositions (`IntervalDecomposition`).
The earlier `PaddedSteps` and `PrimeCycles` lemmas remain checked as well.

## Width three for the direction gadget

The gadget is a subdivision of K4, so its treewidth is three. With the vertex
numbering `B,A,x,z,y,D,C,t,a,u,b,v,w` (ports a,b are 8,10),
[DirectionWidth.lean](TreewidthHom/DirectionWidth.lean) fixes ten bags

```
{a,A,b,C} {b,A,C,D} {A,B,C,D} {u,a,C} {w,b,D} {v,b,w} {y,B,C} {x,B,y} {z,B,D} {t,C,D}
```

with parent bags `-,0,1,0,1,4,2,6,2,1`. The root bag contains both ports. Kernel
evaluation checks that every gadget edge lies in a bag, that bags have at most
four vertices, and that every vertex has a unique topmost bag. For each replaced
arc, a copy of this bag tree is grafted below an existing bag containing both
endpoints. `Graft.running_of_tops` in
[GraftDecomposition.lean](TreewidthHom/GraftDecomposition.lean) turns the
"unique topmost bag" property into the connected-occurrence condition, for
arbitrary (possibly infinite) families of grafted copies. The same lemma gives
the incidence bags `{v,w,t}`, `{v,t,u_1}`, `{w,t,u_2}` of the written proof and
the two-element bags of the target's underlying forest.

Three is the best this construction can give: both final graphs contain the
gadget, hence a K4 minor. It is not claimed optimal for the problem. Targets of
treewidth one are forests, for which the problem is polynomial, so the least
conceivable hard target width is two.

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

## Odd-cycle targets: target width two

[`OddCycle.reduction_cycleGraph`](TreewidthHom/OddCycleReduction.lean) is a
separate reduction, from Multicoloured Clique, whose target is mathlib's
`cycleGraph n` for an odd `n`. For every graph `Γ` on `Fin k × Fin N` it proves:

- `Nonempty (source Γ →g cycleGraph n)` if and only if `Γ` has a clique with one
  vertex in each of the `k` classes;
- a tree-decomposition certificate of width at most `k+2` for the source and of
  width at most `2` for the cycle;
- `n` is odd, and the source has at most `(k+1)^2 * n^2` vertices, where
  `n = 2*(N*(2*N*k+1+k)+2)+1`.

[ODD_CYCLE.md](ODD_CYCLE.md) has the written proof and the file map. This
result does not depend on the LCS constructions below; it shares only the
tree-decomposition infrastructure. Multicoloured Clique's W[1]-hardness is an
external input.

## Arbitrary alphabets

[`BlockLCS.alphabet_full_reduction`](TreewidthHom/BlockReduction.lean) proves, for
words over **any nonempty finite alphabet** `α`, that there is a finite simple
graph pair `(G,H)` with

- `Nonempty (G →g H)` if and only if the words have a common subsequence of
  length `ell` (`CommonSubsequence` is now stated for an arbitrary alphabet);
- the same width certificates: at most `max(2k,3)` for `G` and `3` for `H`;
- at most `10^12 * (s+1)^12` vertices in each graph, where
  `s = k + (clog_2 |α| + 1) * sum_i length(words i) + 1`.

This is the block construction of
[SOLUTION.md, Section 9](SOLUTION.md#9-arbitrary-alphabets-hardness-beyond-w1).
`BlockLCS.full_reduction` is the same statement for letters that are vectors of
`L+1` bits, and `alphabet_reduction` transfers it through any injective code.
The Lean block length is `L+1`, written `L` in the prose. The Lean padding bound
is the total bit length of all words; any bound at least the longest row works.

| File | Principal result | Meaning |
| --- | --- | --- |
| [BlockInstance.lean](TreewidthHom/BlockInstance.lean) | `query`, `target`, `BlockCommon` | Block-encoded structures over the unchanged schema. `Advance` leaves block boundaries only; `Begin` moves inside a block. |
| [BlockEncode.lean](TreewidthHom/BlockEncode.lean), [BlockDecode.lean](TreewidthHom/BlockDecode.lean) | `blockCommon_hom`, `Decode.blockCommon` | Both directions of the relational front end. |
| [BlockWidth.lean](TreewidthHom/BlockWidth.lean) | `query_width`, `target_width` | Source bags of size at most `2k+1`. The target's Gaifman graph is a subgraph of a binary target's, so its bags have size at most four. |
| [BlockReduction.lean](TreewidthHom/BlockReduction.lean) | `blockCommon_iff`, `full_reduction`, `alphabet_full_reduction` | Bit blocks express LCS over the letters; all input cases, widths and size; arbitrary finite alphabets. |

The incidence, prime-cycle and direction stages and their width lemmas are
reused unchanged. This front end is a second, parallel instance: the binary
`LCSInstance` files remain, because the executable constructor and the measured
cost model are built on them. **The executable and cost layers cover binary
words only.**

## Remaining complexity obligations

The combinatorial reduction has no remaining correctness, width, finiteness,
or polynomial-output-size assumptions. The following are outside the current
formal theorem:

1. Justify primitive bit costs and refine the complete measured program to an
   explicit bit-cost or machine model. The abstract cost composition is checked,
   but arithmetic and mapping callbacks still have assigned unit costs, while
   comparisons and word access have an assigned charge `q`. No theorem bounds
   these implementations' physical costs yet. Polynomial output size and
   abstract operation counts do not by themselves close this obligation.
2. Instantiate a formal parameterized-reduction framework and derive the
   hardness conclusions. The published hardness theorems for LCS remain
   explicitly external inputs, not project axioms: Pietrzak for binary strings
   (W[1]), and Bodlaender–Downey–Fellows–Wareham and Elberfeld–Stockhusen–Tantau
   for alphabets given in the input (W[t] for all t, and XNLP). XNLP-hardness
   further needs the reduction to be computable in logarithmic space, which is
   argued in prose only.
3. Optionally sharpen the checked source bound from `2k` to the written `k+1`
   and the coarse size bound to the written sparse quadratic bound. Neither
   improvement changes the intended parameterized-hardness conclusion or the
   final target width 3.

The tree-decomposition certificates use mathlib trees and walks, require vertex
and edge coverage and connected occurrence bags, and bound every finite bag by
width plus one. `HasWidth` packages such a certificate; a minimization-based
graph treewidth function is not defined. Existence of a decidable-equality
instance in this package is bookkeeping for finite sets, not a graph assumption.

## Reproduction and trust

Run `python3 scripts/check_formalization.py`. It builds the library and audits
137 principal declarations in
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
