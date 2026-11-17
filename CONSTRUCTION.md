# List Colouring to odd-cycle homomorphism

The construction transfers List Colouring to ordinary graph homomorphism while
raising treewidth, pathwidth and feedback vertex number by constants. The
[paper](paper/odd-cycle-homomorphism.pdf) contains the complete argument and
complexity-class membership proofs. The [formalisation map](FORMALIZATION.md)
distinguishes checked statements from external results and resource analysis.

## Two lemmas

For odd `n ≥ 5`, every endomorphism of `C_n` is a rotation or reflection.
Its `n` increments are ±1; their sum is an odd multiple of `n` between `-n`
and `n`, so all increments have the same sign.

A path of length `n-2` maps into `C_n` with endpoint images `x,y` exactly when
`x ≠ y`. Its possible displacements are the `n-1` nonzero residues, represented
by `-(n-2), -(n-4), …, n-4, n-2`. Call such a private path a **link**.

## Construction

For List Colouring on `F`, identify the palette with `0,…,q-1` and choose odd
`n ≥ max(5,q+1)`. Introduce hubs `h_v` and a shared edge `AB`.

For each `(v,d) ∈ V(F) × Z_n`, create a reference `n`-cycle whose coordinates
0 and 1 are identified with `A,B`. All other vertices are private. If `d` is
outside the list of `v`, add one link from coordinate `d` of this copy to `h_v`.
For each original edge `uv`, add one link from `h_u` to `h_v`.

Normalise the image of `AB` to `(0,1)`. Rigidity fixes every reference copy,
so the domain links exclude exactly the forbidden colours. The original-edge
links enforce a proper colouring. Conversely, any list colouring extends across
all reference cycles and links. Thus `F` is list-colourable iff `G → C_n`.

Each forbidden occurrence `(v,d)` has its own reference copy and a single
domain link. After deleting `A,B`, that copy becomes a path attached through
at most one link, so it cannot create a new cycle. Copies for allowed colours
have no domain link; retaining them keeps the finite vertex type uniform in
the paper, Lean, and the executable construction.

## Structural bounds

- **Treewidth:** root each private reference path at its domain coordinate
  (or at coordinate 2 for an anchor coordinate), and attach the root to its hub.
  These tree attachments need bags of size two. Adding `A,B` gives bags of
  size four; subdividing the required edges needs bags of size three.
  Result: `tw(G) ≤ max(tw(F)+2,3)`.
- **Pathwidth:** first process each reference cycle with two private vertices
  at a time while retaining its hub and `A,B`, giving `p+4` for the graph with
  direct constraint edges. Subdivide those edges by serial path sweeps, adding
  at most two bag vertices. Result: `pw(G) ≤ pw(F)+6`.
- **Feedback vertex set:** from `S` in `F`, delete its hubs and `A,B`. Original
  links leave a subdivided forest with path fragments; each reference path and
  its optional single link attach to at most one surviving hub. The deleted
  set has size `|S|+2`.

For padded lists, coordinate `n-1` is forbidden at every hub. Contract each
selected reference path and its domain link into its hub, then contract the
original-edge links. This exhibits `K₂ ∨ F` as a minor. If `F` has an edge,
minor monotonicity gives matching lower bounds:

```
tw(G) = tw(F)+2,     fvs(G) = fvs(F)+2.
```

For every nonempty `F`, the same minor also gives
`pw(F)+2 ≤ pw(G) ≤ pw(F)+6`: joining two adjacent universal vertices raises
pathwidth by exactly two, by the Helly property for vertex-occurrence intervals.

Lean checks the branch-set minor, minor monotonicity of all three parameters,
and the matching lower bounds. The exact-transfer theorem explicitly assumes
that every list omits coordinate `n-1`; the generic upper bounds need no such
assumption. See [ListExact.lean](TreewidthHom/ListExact.lean).

For `m=|V(F)|`, `e=|E(F)|` and `f=Σ_v(n-|L(v)|)`,

```
|V(G)| = m+2+mn(n-2)+(e+f)(n-3)
       ≤ 2+m+mn²+(mn+m²)n.
```

The construction and supplied decompositions can be emitted in logarithmic
space using counters and input rescans. The paper gives the resource analysis
and derives the complexity classifications from the published List Colouring
hardness results and the homomorphism membership algorithms.

## Connected, sparse sources

The source is connected: every hub excludes the common unused residue `q`
and therefore has a domain link to the reference component containing `AB`.
For empty input, the source is just `AB`.

It is also 2-degenerate: remove link interiors, then private reference vertices,
leaving `AB` and isolated hubs. For nonempty `F`, its girth is exactly `n`.
The reference cycles have girth `n`; any cycle using links must use at least
two complete links, giving length at least `2(n-2) ≥ n`.
Choosing `n` above any fixed threshold gives the large-girth restriction
without changing the parameter bounds.

## Target encoding and recognition

Binary target lengths suffice: an odd cycle longer than `|V(G)|` admits a
homomorphism from `G` exactly when `G` is bipartite. Thus replacing `n` by
`min(n, 2|V(G)|+5)` preserves the answer and allows a linear-size unary target.

For nonempty input, the constructed graph contains `C_n` and has odd girth `n`.
It therefore has an odd-cycle core exactly when it maps to `C_n`. Discarding
the target gives the same complexity classifications for recognising graphs
whose core is an odd cycle. The paper ensures nonemptiness by adjoining an
isolated vertex with a singleton list prescribing a fresh colour. This preserves
all three input parameters. Membership is proved separately.
