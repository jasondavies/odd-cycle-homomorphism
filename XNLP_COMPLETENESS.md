# Homomorphism to an odd cycle is XNLP-complete with a supplied path decomposition

Deciding whether an undirected graph maps homomorphically to an input odd
cycle is XNLP-complete when a path decomposition of the source is supplied
and its width bound is the parameter. The target has pathwidth and treewidth
two. The hardness reduction produces source pathwidth at most `2k+4` from
Chained Multicolored Clique with `k` colors per layer.

This note gives both the membership algorithm and the chained reduction.
The ordinary-clique reduction is in [ODD_CYCLE.md](ODD_CYCLE.md).
The local-to-global correctness lemma for membership is checked in
[BagHomomorphism.lean](TreewidthHom/BagHomomorphism.lean). The chained
construction and the machine time/space bounds below are mathematical proofs,
not Lean complexity theorems.

## Exact problem and theorem

An instance consists of:

- a finite simple undirected graph `G`, explicitly represented;
- an odd integer `n >= 3`, represented in unary, specifying the target `C_n`;
- an explicit sequence of bags `B_1,...,B_l`, with `l >= 1`, and a nonnegative
  width bound `w`.

The parameter is `w`. Accept precisely when the bags form a path
decomposition of `G` of width at most `w` and a homomorphism `G -> C_n`
exists. Malformed inputs and invalid decomposition certificates are rejected.
An empty graph can be represented with one empty bag.

**Theorem.** This parameterized problem is XNLP-complete under parameterized
logspace reductions, even restricted to `n >= 5`.

Equivalently, one can promise a valid supplied decomposition and use its
width as parameter. Supplying an explicit cycle instead of unary `n` gives
the same result. The length of the target cycle is not fixed and is not a
parameter.

The supplied-decomposition convention matters. This proof establishes
XNLP-hardness when only the graph and its source-pathwidth parameter are
given, but does not establish membership for that version. It also does not
claim XNLP-membership for the source-treewidth parameterization. The standard
XNLP reference adopts the same supplied-decomposition convention
([Bodlaender et al., Section 2.4 and Theorem 13][bgns]).

## Membership in XNLP

Let `L >= 2` be the total encoded input length. Vertex indices, target
residues, and input positions require `O(log L)` bits. XNLP permits
nondeterministic time `f(w) L^c` and work space `f(w) log L`, for a computable
function `f` and a constant `c` independent of `w`.
Use indices into the explicit vertex list. An oversized binary width bound
can be capped at `L` while parsing, since no explicitly listed bag can have
more than `L` entries; this avoids storing a large integer just to validate it.

First validate the decomposition deterministically by rescanning the
read-only input:

1. Check the graph and bag encodings, vertex identifiers, absence of duplicate
   entries within a bag, and `|B_i| <= w+1` for each bag.
2. For each source vertex, scan the bag sequence and check that it occurs
   at least once, with no occurrence after its occurrence interval has ended.
3. For each source edge, find a bag containing both endpoints.

Only counters, a constant number of vertex identifiers, and a three-state
occurrence flag are needed. These nested scans use `O(log L)` work space and
polynomial time. The supplied bags are never copied in their entirety to
work space during this validation.

Then process the bags from left to right. For each bag `B_i`:

1. Guess a residue `a_i(v)` in `{0,...,n-1}` for every vertex `v` in the bag.
   Store these vertex-image pairs, retaining the preceding bag's pairs.
2. For every vertex in `B_(i-1) intersect B_i`, check that its two guessed
   images agree.
3. For every source edge with both endpoints in `B_i`, check that the images
   differ by `+1` or `-1` modulo `n`.
4. Discard the preceding bag's pairs and continue.

Accept if every check succeeds. No table of all possible bag assignments is
constructed: a computation branch guesses just one assignment per bag.

**Soundness.** The bags containing a fixed vertex form an interval. Equality
across consecutive overlaps therefore makes all occurrences of that vertex
agree. These values define a single function on the source vertices. Every
edge occurs in a bag, and its local check ensures that the function preserves
that edge. Thus an accepting branch determines a homomorphism.

**Completeness.** Restrict any homomorphism to each bag. Guessing these
restrictions passes all overlap and edge checks.

**Resources.** At most `2(w+1)` vertex-image pairs are stored simultaneously,
along with `O(log L)` bits of counters and arithmetic workspace. Thus space
is `O((w+1) log L)`. Every stored image uses `O(log n) <= O(log L)` bits.
All bag occurrences and edges are explicitly encoded, so the comparisons
and rescans take polynomial time with a degree independent of `w`. Guessing
a residue uses its binary representation and rejects an out-of-range guess.
Both XNLP bounds hold simultaneously, establishing membership.

The argument works for any explicitly represented target graph; odd-cycle
adjacency simply makes the edge check especially direct.

## Chained hardness reduction

Chained Multicolored Clique is XNLP-complete under parameterized logspace
reductions ([Bodlaender et al., Theorem 11][bgns]). Its input has layers
`V_1,...,V_r` and `k` colors in each layer. One must select one vertex of each
color in each layer so that the selected vertices in every consecutive pair
of layers form a clique. We use the hard restriction `r >= 2`, `k >= 1`.
Handle an empty layer-color class by outputting the fixed no-instance
`K_3 -> C_5`, with its one-bag width-two source decomposition. Otherwise pad
classes with isolated vertices to a common size `N >= 1`. A padded vertex
cannot belong to a feasible selection, since it must be adjacent to selected
vertices in a neighboring layer.

Let `s=(t,c)` index a layer-color class, in lexicographic order. Two classes
form a *required pair* if they are distinct classes in one layer or are in
consecutive layers. There are no constraints between nonconsecutive layers.

### Labels and links

Set `K=rk`. Assign the `K` classes indices `s=0,...,K-1` and use the existing
elementary labels with that class count:

    Q = 2NK+1,
    lambda_s(a) = a(Q+s),       1 <= a <= N,
    M = N(Q+K)+2,
    n = 2M+1.

For any two distinct classes, a difference of labels determines both labels
uniquely, and cannot equal the negative of another difference for that
ordered pair. This is precisely the arithmetic lemma from
[ODD_CYCLE.md](ODD_CYCLE.md#correctness), now applied with `K` classes.
All labels are at most `M-2`, so the modular equalities involved unwrap to
integer equalities because `n > 2M`.

A *link* is a path of length `n-2` with fresh internal vertices. Such a path
maps into `C_n` with specified endpoint images exactly when those images
are distinct. Every homomorphism `C_n -> C_n` is a rotation or reflection.
Both facts are proved in [ODD_CYCLE.md](ODD_CYCLE.md#two-facts-about-odd-cycles)
and checked in `OddCycleTarget.lean`.

### Source graph

For each class `s` make a private choice cycle `F_s=C_n`, with coordinate
vertices `f^s_d` and hub `h_s=f^s_0`.

For each layer `t` make a reference cycle `R_t=C_n`. Identify coordinate
zero of every reference cycle to a single vertex `A`, and coordinate one
of every reference cycle to a single vertex `B`. Apart from this shared edge
`AB`, the reference cycles are disjoint. They are disjoint from the choice
cycles.

For class `s=(t,c)`, let `Lambda_s` contain its vertex labels. For every
residue `d` outside `Lambda_s`, add a link from coordinate `d` of `R_t` to
`h_s`.

For each required pair `s<u`, let

    D_su = {lambda_u(b)-lambda_s(a) mod n : ab is an input edge}.

For every residue `d` outside `D_su`, add a link from `f^s_d` to `h_u`.
All link interiors are private. Do not add links for nonrequired pairs.
The target is the single odd cycle `C_n`.

### Correctness

Suppose a source homomorphism exists. Normalize its image of the shared
edge so that `A` maps to zero and `B` to one. Each reference cycle then maps
by coordinate identity: its restriction is a rotation or reflection, and
fixing that ordered edge determines the identity. Thus all reference cycles
use the same coordinates.

Class links force `h_s` to the label of a selected vertex `a_s`. On a choice
cycle the map consequently has the form

    f^s_d -> lambda_s(a_s) + epsilon_s d,    epsilon_s in {+1,-1}.

For every required pair `s<u`, its links imply

    epsilon_s (lambda_u(a_u)-lambda_s(a_s)) in D_su.

The existing signed-difference lemma forces the selected vertices to be
the endpoints of an actual input edge. This holds for every required pair,
so the selections constitute a chained multicolored clique.

Conversely, given such a clique, map every reference cycle by identity and
every choice cycle by rotation through its chosen label. Each link has
distinct endpoint images by its definition, so each extends to a walk of
length `n-2`. This constructs a homomorphism of the entire source graph.

### Supplied path decomposition

Process layers in order. During phase `t`, retain

    S_t = {A,B} union {h_(u,c) : u=t or u=t+1, u<=r, 1<=c<=k}.

This set has size at most `2k+2`. Traverse `R_t`, then the choice cycles of
layer `t`, each in coordinate order. At each current cycle vertex `x`,
process all links whose designated start is that occurrence of `x`. Their
other endpoints are hubs in `S_t`. Process the links one at a time, using
bags containing `S_t`, `x`, and two consecutive vertices of the link.
Use `S_t union {x,x_next}` for successive cycle edges. Closing edges are
covered because the reference anchors and the choice hubs remain in `S_t`.

All edges and vertices are covered. A private link vertex appears during
its link traversal; a private cycle vertex appears during its visit and
the adjacent cycle-edge bags. A hub remains present through its current
and preceding phase, when that preceding phase exists. The anchors `A,B`
remain present throughout. Every occurrence set is therefore an interval.
The next layer's hubs persist across phase boundaries; the older hubs are
forgotten before introducing the following layer's hubs.

Bags have at most `2k+5` vertices, yielding a path decomposition of width
at most `2k+4`. The target has the width-two path decomposition with bags
`{0,d,d+1}` for `d=1,...,n-2`.

### Size and reduction space

There are `rk` choice cycles, `r` reference cycles sharing two vertices,
`rk` class constraints, and
`r*binom(k,2)+(r-1)*k^2` required pairs. Each constraint adds at most `n`
links, each of size `O(n)`. Source size is `O(r k^2 n^2)`. Since
`n=O(N^2 rk)` and nonempty classes are explicitly represented, the output
size is polynomial in the input length. The decomposition has polynomial
size as well.

A logspace transducer enumerates layers, classes, residues, and internal
link positions using a constant number of counters. It computes labels
arithmetically and tests membership in `D_su` by rescanning input edges;
it never stores a full difference set. Use tuple vertex identifiers, or
recompute sequential identifiers by rescanning. Every identifier and
counter has logarithmic length. The bags above can likewise be emitted
one vertex at a time, including their persistent hub sets, without storing
an entire bag. These are polynomial-time, logarithmic-space computations.
The output width bound is `2k+4`, a function of the source parameter alone.
This proves the required parameterized logspace reduction.

Combining hardness with the membership algorithm proves XNLP-completeness
for the exact supplied-decomposition problem stated above. By
[Bodlaender et al., Lemma 2][bgns], XNLP-hardness also implies W[t]-hardness
for every fixed positive `t`.

## Formalization boundary and verification

`Decomposition.hom_iff_bagAssignments` proves that a homomorphism exists
exactly when there are bag assignments that preserve local edges and agree
on overlaps of adjacent decomposition nodes.
`Decomposition.hom_iff_pathBagAssignments` specializes this equivalence to
the membership algorithm's consecutive-bag checks on a path decomposition.
`Decomposition.two_bag_records_le` proves the `2(w+1)` bound on the number
of stored vertex-image records. These are combinatorial statements, not a
formal Turing-machine implementation or a Lean definition of XNLP.

The generic gluing theorem also holds for tree decompositions. This alone
does not give XNLP membership parameterized by treewidth: checking a
branching decomposition with the same time and space bounds needs an
additional algorithm, which is not supplied here.

The previous review's chained prototype checked 373 instances, comparing
full-graph homomorphism with exhaustive clique choices and checking explicit
path decompositions. It used parity-reused prime labels, which satisfy the
same signed-difference property; the present elementary labels align with
the existing Lean reduction. Those finite checks support the construction
but do not establish its general correctness or its complexity bounds.

Reproduce the membership lemma's checks with:

```sh
lake build TreewidthHom.BagHomomorphism
lake env lean BagHomomorphismAudit.lean
```

No novelty or priority claim is made here; see the attribution in
[README.md](README.md).

[bgns]: https://doi.org/10.1016/j.ic.2024.105195
