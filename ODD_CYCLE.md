# List Coloring to odd-cycle homomorphism

The construction transfers List Coloring to ordinary graph homomorphism while
raising treewidth, pathwidth and feedback vertex number by constants. The
[paper](paper/odd-cycle-homomorphism.pdf) contains the complete argument and
complexity-class membership proofs. The [formalization map](FORMALIZATION.md)
distinguishes checked statements from external results and resource analysis.

## Two lemmas

For odd `n ≥ 5`, every endomorphism of `C_n` is a rotation or reflection.
Its `n` increments are ±1; their sum is an odd multiple of `n` between `-n`
and `n`, so all increments have the same sign.

A path of length `n-2` maps into `C_n` with endpoint images `x,y` exactly when
`x ≠ y`. Its possible displacements are the `n-1` nonzero residues, represented
by `-(n-2), -(n-4), …, n-4, n-2`. Call such a private path a **link**.

## Construction

For List Coloring on `F`, identify the palette with `0,…,q-1` and choose odd
`n ≥ max(5,q+1)`. Introduce hubs `h_v` and a shared edge `AB`.

For each `(v,d) ∈ V(F) × Z_n`, create a reference `n`-cycle whose coordinates
0 and 1 are identified with `A,B`. All other vertices are private. If `d` is
outside the list of `v`, add one link from coordinate `d` of this copy to `h_v`.
For each original edge `uv`, add one link from `h_u` to `h_v`.

Normalize the image of `AB` to `(0,1)`. Rigidity fixes every reference copy,
so the domain links exclude exactly the forbidden colors. The original-edge
links enforce a proper coloring. Conversely, any list coloring extends across
all reference cycles and links. Thus `F` is list-colorable iff `G → C_n`.

A separate reference copy for each forbidden color is essential to the feedback
vertex set argument. Copies for allowed colors are harmless and retained in Lean
to keep the finite vertex type uniform.

## Structural bounds

- **Treewidth:** add `A,B` to the original bags. A reference gadget with boundary
  `{A,B,h_v}` becomes a forest after deleting that boundary, so attach its
  forest bags augmented by the boundary. Result: `tw(G) ≤ max(tw(F)+2,4)`.
- **Pathwidth:** first process each reference cycle with two private vertices
  at a time while retaining its hub and `A,B`, giving `p+4` for the graph with
  direct constraint edges. Subdivide those edges by serial path sweeps, adding
  at most two bag vertices. Result: `pw(G) ≤ pw(F)+6`.
- **Feedback vertex set:** from `S` in `F`, delete its hubs and `A,B`. Original
  links leave a subdivided forest with path fragments; each reference path and
  its optional single link attach to at most one surviving hub. The deleted
  set has size `|S|+2`.

For `m=|V(F)|`, `e=|E(F)|` and `f=Σ_v(n-|L(v)|)`,

```
|V(G)| = m+2+mn(n-2)+(e+f)(n-3)
       ≤ 2+m+mn²+(mn+m²)n.
```

The construction and supplied decompositions can be emitted in logarithmic
space using counters and input rescans. The source is 2-degenerate and, for
nonempty `F`, has girth exactly `n`. Choosing `n` above any fixed threshold
therefore gives the large-girth restriction without changing the parameter bounds.

## Complexity consequences

Published List Coloring results give:

- XNLP-completeness for supplied path decompositions: [Bodlaender et al. 2024,
  Theorem 15](https://doi.org/10.1016/j.ic.2024.105195).
- XALP-completeness for supplied tree decompositions: [Bodlaender et al. 2022,
  Theorem 8](https://doi.org/10.4230/LIPIcs.IPEC.2022.6).
- W[3]-hardness for feedback vertex number: [Bodlaender et al. 2023,
  Table 1](https://doi.org/10.4230/LIPIcs.ICALP.2023.27).

The reduction transfers hardness. Membership comes from guessing consistent
bag assignments: retain successive assignments on paths; use an auxiliary
stack when traversing a tree. Working space is `O((w+1) log N)` and total time
is polynomial. The target length is given explicitly or in unary.

Every target has treewidth and pathwidth 2. Width 1 cannot give such hardness:
homomorphism into forests is polynomial-time decidable. The target cycle is
variable, not fixed, and the source width is not a fixed constant.
