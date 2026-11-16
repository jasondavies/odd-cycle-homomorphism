# Homomorphism is W[1]-hard when both treewidths are bounded by the parameter

**Lean status, 2026-11-16:** the complete combinatorial reduction is checked,
including all input cases, both width bounds, and polynomial output size.
The formal proof has the same target bound three as this written argument. It
uses the sufficient source bound `max(2k,3)` and a coarse degree-12 size bound;
this written argument retains its sharper source and size bounds. The
arbitrary-alphabet reduction of Section 9 is checked in the same way. The formal machine-time and W[1]-hardness conclusion
remain outside the library; see [FORMALIZATION.md](FORMALIZATION.md).

**Public-status check, 2026-11-12:** Still in the main source list and the
[Stack Exchange question](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth)
has zero answers, confirmed through the live API. However,
[Amarilli's comment of 2025-05-30](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth#comment124806_34877)
announces W[1]-hardness reductions by other workshop participants. Targeted
searches did not locate their public proof. Thus this is an already-announced
resolution with an unlocated proof, not a safely unclaimed open problem.
The earlier notes already recorded that announcement; the later concise recap
should have made it explicit. Our reduction remains a local proof whose
relationship to that prior work, and whose novelty, have not been established.
This status check does not re-audit its correctness.

Entry a3nm-032. Local proof completed 2026-10-25; independent review and
novelty assessment pending.

**The answer to the FPT-versus-W[1]-hardness question is W[1]-hard.** This
holds for ordinary simple undirected graphs, with no colors, directions,
lists, constants, or designated vertices in the final instance. In fact,
the target graph can always have treewidth at most 3. (An earlier version of
this write-up stated 12, from a cruder decomposition of the same graphs.)

Thus an algorithm taking time f(t) N^c, for a computable f and a constant c,
where t bounds both input treewidths and N is the input size, would imply
FPT=W[1]. This resolves the alternative posed in the
[linked graph-homomorphism question](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth)
and gives the same negative FPT answer to the
[main query-evaluation entry](https://a3nm.net/work/research/questions/#complexity-of-query-evaluation-parameterized-by-treewidth).
[Section 9](#9-arbitrary-alphabets-hardness-beyond-w1) strengthens this: starting
from LCS over an arbitrary alphabet, the same construction gives W[t]-hardness
for every t, and XNLP-hardness, still with target treewidth at most 3. The
combinatorial reduction behind that extension is checked in Lean as well.
We do **not** claim W[1]-membership or W[1]-completeness. The standard
tree-decomposition algorithm supplies an XP upper bound.

The external hardness starting point is binary longest common subsequence
(LCS), parameterized by the number of input strings: this is W[1]-hard by
[Pietrzak, Theorem 2 and Section 4](https://crypto.ethz.ch/publications/files/Pietrz03.pdf),
published in JCSS 67(4), 757–771 (2003),
[DOI](https://doi.org/10.1016/S0022-0000(03)00078-3).
The 13-vertex direction gadget below is G_1 from
[Eleftheriadis, Definition 2.6 and Fact 2.7](https://api.repository.cam.ac.uk/server/api/core/bitstreams/c66b1b4c-bcb5-45aa-af1e-a3b5a9680ec3/content),
*Universal slices of the category of graphs*, Algebra Universalis 85:42
(2024), which credits Hell–Nešetřil. We give the needed gadget proof here.
Neither the hardness theorem nor the gadget is claimed as new.

**Formalisation boundary:** Lean verifies the complete combinatorial reduction
from LCS to simple undirected graph homomorphism, with width and vertex-count
bounds. The machine-time claim and the complexity conclusion remain outside
Lean. See [FORMALIZATION.md](FORMALIZATION.md).

## 1. The reduction and parameter bounds

Start with k>=1 binary strings w_1,...,w_k and a required subsequence length
ell. Empty subsequences are trivial yes-instances; ell greater than the
shortest input length is a trivial no-instance. Map these directly to fixed
yes/no graph pairs. Otherwise put n_i=|w_i| and N=max_i n_i, so
1<=ell<=min_i n_i.

We construct, in succession:

| Stage | Source width | Target width |
| --- | ---: | ---: |
| Fixed-schema relational structures Q,I | <=k+1 | <=3 |
| Typed incidence digraphs | <=max(k+1,2) | <=3 |
| Uncolored, loopless digraphs D_Q,D_I | <=max(k+1,2) | <=3 |
| Simple undirected graphs G,H | <=max(k+1,3) | <=3 |

Each stage preserves existence of a homomorphism in both directions. For
digraphs and relational structures, width means the treewidth of the
underlying Gaifman graph. All decompositions can be produced explicitly.
The source size is O(k ell N), the target size O(sum_i n_i+k), and the
later stages increase sizes by fixed constants. Because k ell<=sum_i n_i,
the entire construction has at most quadratic size in the LCS input length.

## 2. LCS as a bounded-width relational homomorphism

Use one fixed unary relation Root and five fixed binary relations
Next, Begin, Step, Advance, and Letter. The alphabet does not change the
schema. The target structure I has:

- Anchor vertices a_0,...,a_k, with Root(a_0) and Next(a_(i-1),a_i).
- A path of position vertices p_(i,0),...,p_(i,n_i) for each string, with
  Begin(a_i,p_(i,0)). Position zero is a sentinel before the string.
- Step(p_(i,j),p_(i,j)) at every position, and both
  Step(p_(i,j-1),p_(i,j)) and Advance(p_(i,j-1),p_(i,j)) for j>=1.
- Two letter vertices b_0,b_1, omitting one if its symbol never occurs, and
  Letter(p_(i,j),b_(w_i[j])) for every genuine position j>=1.

There are no other facts. Deleting the letter vertices from the Gaifman
graph leaves a tree: the anchor path with one position path attached to
each noninitial anchor. Add the at most two letter vertices to every bag
of a width-one decomposition of that tree. This gives tw(I)<=3.

Construct Q with its own anchor path c_0,...,c_k carrying Root and Next
facts, and initial position variables x_(i,0) with Begin(c_i,x_(i,0)).
For each subsequence position j=1,...,ell introduce a common letter variable
z_j. For every string i, connect x_(i,j-1) to x_(i,j) by a fresh chain of
exactly N Step edges followed by one Advance edge, and include
Letter(x_(i,j),z_j).

The anchor path must map to a_0,...,a_k, since Root and Next fix its image
successively. Begin then fixes every x_(i,0) to the appropriate sentinel.
A Step chain can stay at its current position or move forward by one at
each edge; it cannot leave the corresponding string path. The final
Advance forces at least one forward move between consecutive selections.
Thus any homomorphism selects ell strictly increasing positions in every
string. All selected positions at step j have the letter specified by z_j,
so the images of z_1,...,z_ell spell a common subsequence.

Conversely, given such a common subsequence, map each x_(i,j) to its chosen
occurrence and each z_j to the corresponding letter vertex. A gap of d>=1
positions is realized by d-1 forward Step moves, the necessary stays to
make N Step moves, and one Advance. Since d-1<=N, this is always possible.
All facts are respected. Therefore

    Q -> I  iff  the strings have a common subsequence of length ell.

For a path decomposition of Q, first traverse the anchor path while
retaining the initial position variable already created for each string.
This needs bags of size at most k+1. Then keep one current position per
string. While processing j, also keep z_j, and process the k chains one
at a time. Each edge needs just the k current positions, z_j, and the new
vertex; afterwards replace the old position by the new one. Bags have
size at most k+2. Forget z_j after all k Letter facts are covered. Every
variable's bags form an interval, so this proves pathwidth(Q)<=k+1.

Already this proves W[1]-hardness of CQ evaluation over a fixed schema with
database treewidth at most three. The next stages remove the schema and
directions to cover the unlabelled graph formulation as well.

## 3. Encode relation names and argument positions

For a structure A, make a vertex of type Domain for each element. For each
fact R(v_1,...,v_r), create a tuple vertex t of type Tuple_R, and distinct
port vertices u_1,...,u_r of types Port_(R,1),...,Port_(R,r). Insert arcs

    t -> u_i -> v_i, for i=1,...,r.

There are 18 types, since the schema has one unary and five binary
relations. All arcs join different types, and the digraph is acyclic with
three layers. Every vertex has an incident arc on the instances above.

A type-preserving homomorphism of these incidence digraphs restricts to
a homomorphism of structures: the image of each tuple vertex determines
a target fact, and its typed ports force the ordered arguments. Conversely,
every structural homomorphism extends in this way.

For a unary fact at v, attach bags covering its length-two incidence path
to a bag containing v. For a binary fact (v,w), start at a bag containing
its arguments, attach {v,w,t}, then {v,t,u_1} and {w,t,u_2}. This also works
when v=w. These added bags have size at most three. Thus the new width is
at most max(old width,2).

## 4. Remove the 18 vertex types with directed prime cycles

Assign the types distinct primes from

    3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67.

At every typed vertex v attach a directed cycle of its type's prime length,
identifying one cycle vertex with v. Call v its root. Keep all incidence
arcs, then erase the types.

The strongly connected components of the resulting digraph are exactly
the attached cycles. Indeed, contracting them recovers the acyclic incidence
digraph. A directed cycle of length p can map into a directed cycle of
length q only if q divides p. All lengths are distinct primes, so any
homomorphism preserves the cycle type. On a cycle of equal length it is
a rotation.

Every original incidence vertex has an arc to a vertex of a different
type. Images of such an arc lie in two distinct components, and the only
arcs between components join roots. It follows that every incidence vertex
maps to a root. Its color is preserved, so the original typed incidence
homomorphism is recovered. The converse extends a typed map around each
cycle. No new homomorphism existence is introduced.

An attached cycle has a width-two decomposition whose bags all include
its root. Attach that decomposition to an existing bag containing the root.
Consequently the width remains at most max(old width,2). Both resulting
digraphs are loopless and have no isolated vertices.

## 5. An explicit undirected direction gadget

Let F be a subdivision of K_4 with branch vertices A,B,C,D and these
internally disjoint paths:

| Branch pair | Path | Length |
| --- | --- | ---: |
| A,B | A B | 1 |
| A,C | A a u C | 3 |
| A,D | A b v w D | 4 |
| B,C | B x y C | 3 |
| B,D | B z D | 2 |
| C,D | C t D | 2 |

The two ordered ports are a,b. There are 13 vertices and 15 edges.
Its simple cycles correspond to the four triangles and three four-cycles
of K_4, and have lengths

    ABC:7, ABD:7, BCD:7, ACD:9;
    ABCDA:10, ABDCA:8, ACBDA:12.

Thus F has girth and odd girth seven. Its three seven-cycles cover all vertices and
edges. Their pairwise intersections are the AB, BC, and BD paths, of
distinct lengths 1,3,2, respectively.

### Rigidity: every endomorphism of F is the identity

Every homomorphism of a seven-cycle into an odd-girth-seven graph is
injective on that cycle. Otherwise its closed walk splits at a repeated
vertex, producing an odd closed walk shorter than seven, which contains
a shorter odd cycle.

Every pair of edges incident with B occurs in one of the three seven-cycles.
Their images must therefore be three distinct edges incident with the image
of B. Among the four degree-three branch vertices, B is the only one for
which all three incident pairs belong to seven-cycles. Vertices of degree
two cannot accommodate the three distinct edges. Hence B maps to B.

The three seven-cycles are permuted: their incident edge pairs at B are
distinct and determine the three possible seven-cycles. For each pair of
cycles, their common path maps injectively into the intersection of their
image cycles. Its length cannot exceed that target intersection's length.
These inequalities permute the same multiset {1,2,3}, so all are equalities.
As the lengths are distinct, every cycle pair is fixed, hence each cycle
is fixed. In particular AB is fixed and B is fixed, so A is fixed. An
automorphism of a cycle fixing adjacent vertices is the identity. This
fixes ABC and ABD pointwise, and then BCD as well. All of F is fixed.

### Odd paths between the ports have length at least seven

There is a two-edge path a A b. Suppose a simple odd a-b path has length
at most five. If it contains A, a non-direct segment between a port and A,
together with their edge, would form a cycle of length less than seven;
if both segments are direct the path has even length two. Both cases fail.
If it avoids A, adjoining a A b forms an odd cycle of length at most seven.
Odd girth excludes lengths below seven, and the cycle list shows that no
seven-cycle uses both A a and A b. This is also impossible.

### Every gadget homomorphism stays inside a single gadget copy

For a loopless digraph D, construct D*F by replacing each arc (r,s) by a
fresh copy of F whose ports a,b are identified with r,s, in that order.
All other gadget vertices are private to that copy. Since a,b are not
adjacent, distinct copies share no edge.

A simple cycle crossing between copies consists of port-to-port segments.
Each has length at least two. If the cycle is odd, some segment is odd
and has length at least seven, so the cycle has length at least nine.
Thus D*F has odd girth at least seven, and every seven-cycle lies in one
copy of F.

Under a homomorphism F -> D*F, each of F's three seven-cycles must map
injectively onto a seven-cycle in a copy. The source cycles intersect
pairwise in edges. Their image copies must coincide, since distinct copies
share no edge. As the three cycles cover F, its whole image lies in one
copy. Rigidity makes the map to that copy the identity in gadget coordinates.

## 6. Remove all directions, and bound the final widths

Replace every arc of D_Q and D_I with F as above, obtaining G and H.
A digraph homomorphism extends over copies of F by their coordinates.
Conversely, the preceding argument forces every source copy into a target
copy with the ordered ports preserved. Every source digraph vertex has
an incident arc, so it maps to a target digraph vertex; the induced map
preserves every directed arc. Consequently

    G -> H  iff  D_Q -> D_I  iff  Q -> I  iff  LCS >= ell.

These are simple undirected loopless graphs. The gadget F is a subdivision
of K_4 and has the following tree decomposition of width three, whose root
bag contains both ports:

    {a,A,b,C}                      root
    ├─ {u,a,C}
    └─ {b,A,C,D}
       ├─ {w,b,D} ── {v,b,w}
       ├─ {t,C,D}
       └─ {A,B,C,D}
          ├─ {y,B,C} ── {x,B,y}
          └─ {z,B,D}

Each of the 15 edges lies in a bag, and each vertex's bags form a subtree.
To extend a decomposition of an underlying digraph, take for every replaced
arc (r,s) a copy of this bag tree, with a,b renamed to r,s, and attach its
root to an existing bag containing r and s. Private gadget vertices occur
only inside their copy. An old vertex occurs in a copy only as a port; its
bags there form a subtree containing the copy's root, which is adjacent to
an old bag containing it. So each old vertex's bags stay connected, and the
width is at most max(old width,3). Therefore

    tw(G) <= max(k+1,3),    tw(H) <= 3.

Because G and H contain F, and hence a K_4 minor, this construction cannot
give less than three. We do not claim that three is optimal for the problem:
a target of treewidth one is a forest, for which homomorphism is polynomial,
so two is the least width a hard target could have.

This is a polynomial-time, parameter-preserving many-one reduction from
binary LCS parameterized by k. Pietrzak's theorem proves the claimed
W[1]-hardness. An FPT algorithm parameterized by both treewidths would
give an FPT algorithm for that LCS problem, implying FPT=W[1]. **QED.**

## 7. Reproduction, scope, and attribution

[bounded_width_hom_hardness.py](scripts/bounded_width_hom_hardness.py)
implements every construction and outputs explicit tree decompositions.
The function `reduce_lcs_to_graphs(words, length)` includes the trivial
input cases. The code is a reduction, not an efficient solver for the
resulting hard homomorphism instances.

[run_bounded_width_hom_checks.py](scripts/run_bounded_width_hom_checks.py)
uses independent finite oracles. It compares relational homomorphism
existence with direct common-subsequence enumeration, exhausts the gadget's
endomorphisms and simple cycles, checks prime-cycle encodings, tests maps
into composite gadget graphs, and verifies the final graph decompositions
and extensions of positive homomorphisms.

The retained run passes 9,330 LCS/relational-homomorphism comparisons. Of
these 5,482 are binary: all ordered one-, two-, and three-string instances with
nonempty strings of length at most three and all nontrivial required lengths,
plus 60 larger seeded cases. The other 3,848 use the block encoding of
Section 9: all one- and two-string instances over three letters with strings
of length at most three, plus 200 seeded cases over three to eight letters. It also checks 36 prime-encoding pairs and
all 192 gadget maps into the replacements of 63 nonempty three-vertex
digraphs. Eight complete constructions, three of them over a three-letter
alphabet, have their final decompositions validated, including graphs of up
to 90,402 vertices. Positive maps are
extended and checked edge by edge; the three complete negative examples rely
on the proved converse, rather than an infeasible unrestricted search over
their large final graphs.

[Recorded results](sources/bounded-width-hom-results.json).
The general converse implications and width bounds are proved above, not
inferred from finite tests.

The author's May 2025 comment already announced forthcoming W[1]-hardness
from workshop discussions. We did not locate that reduction or establish
whether it is the same one. This write-up provides a complete locally
checked argument, with established ingredients credited. It does not
establish publication priority. Independent external review remains pending.

## 8. A kernel-checked alternative confinement argument

The Lean proof uses a shorter route to confinement than Section 5. Identify the
two ports in F, obtaining a quotient Q. A complete kernel-checked enumeration
finds eight maps F → Q. For every such map, the preimage of Q's non-port vertices
is nonempty and connected, and every remaining vertex has a neighbor in it.

In any assembly of copies, project all glued endpoints to Q's identified port
and every private vertex to its gadget coordinate. For any map from F into the
assembly, its composition with this projection is one of the eight checked
maps. Adjacency between private vertices forces equality of their copy indices.
Connectivity therefore places every private image in a single copy. The neighbor
property places every other image in that copy as well. Each copy is an induced
embedding, so rigidity gives its coordinate-preserving inclusion.

This proves confinement for arbitrary assemblies, without a size bound. It is
formalised in [ArrowConfinement.lean](TreewidthHom/ArrowConfinement.lean), using
[the finite quotient certificate](TreewidthHom/ArrowQuotient.lean). It does not
change the graph construction or the width constants in the written reduction.

## 9. Arbitrary alphabets: hardness beyond W[1]

For LCS over a fixed alphabet, parameterized by the number of strings, only
W[1]-hardness is known to us. When the alphabet is part of the input, the same
problem is much harder:

- it is W[t]-hard for every t
  (Bodlaender, Downey, Fellows, Wareham, *The parameterized complexity of
  sequence alignment and consensus*, Theoretical Computer Science 147 (1995)
  31–54);
- it is XNLP-complete (Elberfeld, Stockhusen, Tantau, *On the space and circuit
  complexity of parameterized problems: classes and completeness*,
  [Algorithmica 71 (2015) 661–701](https://doi.org/10.1007/s00453-014-9944-y),
  as stated in
  [Bodlaender, Groenland, Nederlof, Swennenhuis](https://arxiv.org/abs/2105.14882),
  Sections 2.4 and 5.1). XNLP-hardness implies W[t]-hardness for every t
  (their Lemma 2).

A larger alphabet cannot simply be added to Section 2: one letter vertex per
symbol would put the target width at |Sigma|+1. No parameter-preserving
reduction from general to binary LCS is known to us either. Instead we encode
letters in binary *inside* the target rows. The schema, the 18 types, all
later stages and both width bounds stay as they are.

### Construction

Let Sigma be the set of letters that occur, L = max(1, ceil(log_2 |Sigma|)),
and fix an injective code c : Sigma -> {0,1}^L. Replace every string w_i by
the bit string w'_i = c(w_i[1]) ... c(w_i[n_i]) of length L n_i. Bits
(a-1)L+1,...,aL form *block* a. Call a position p_(i,m) a *boundary* if L
divides m; the sentinel p_(i,0) is a boundary.

The target I' is the structure I of Section 2 for w'_1,...,w'_k, with one
change to the facts on each row edge (p_(i,m-1), p_(i,m)):

- Step is present on every row edge, and as a loop at every position, as before;
- Advance is present only when p_(i,m-1) is a boundary, so it *enters* a block;
- Begin is present when p_(i,m-1) is not a boundary, so it moves *inside* a block.

Letter(p_(i,m), b) holds for the bit b = w'_i[m], with at most two bit
vertices b_0, b_1. Reusing Begin avoids a new relation; a fresh relation
would work equally well.

The query Q' keeps the anchor path and the initial variables x_(i,0). For each
j = 1,...,ell it has L shared variables z_(j,1),...,z_(j,L). For every string i
it joins x_(i,j-1) to x_(i,j) by

- a chain of exactly N = L max_i n_i Step edges, then
- one Advance edge to a new vertex y_(i,j,1), then
- L-1 Begin edges y_(i,j,1) -> ... -> y_(i,j,L) = x_(i,j),

with Letter(y_(i,j,t), z_(j,t)) for t = 1,...,L. For L = 1 this is exactly the
construction of Section 2.

### Correctness

The anchors are forced as before: Root and Next do not occur on rows, and the
only Begin-successor of a_i is p_(i,0). So x_(i,0) maps to p_(i,0).

Suppose x_(i,j-1) maps to the boundary p_(i,aL). The Step chain stays on row i
and ends at some p_(i,m) with m >= aL. An Advance edge leaves only a boundary,
so m = bL with b >= a, and y_(i,j,1) maps to p_(i,bL+1). A non-boundary
position p_(i,m') has exactly one Begin-successor, p_(i,m'+1). Hence
y_(i,j,t) maps to p_(i,bL+t), and x_(i,j) maps to the boundary p_(i,(b+1)L).
The query thus selects in each string strictly increasing blocks, and reads
all L bits of each selected block. The Letter facts force z_(j,t) to the t-th
bit of the selected letter's code, for every string i. As c is injective, all
strings select the same letter at step j. So a homomorphism yields a common
subsequence of length ell.

Conversely, map each x_(i,j) to the end of the block of the chosen occurrence
and each z_(j,t) to the corresponding code bit. Moving on by d >= 1 blocks
takes (d-1)L forward Step moves, padded with stays to exactly N, then Advance
and L-1 Begin moves. Therefore

    Q' -> I'  iff  the strings have a common subsequence of length ell.

### Widths and size

Deleting the bit vertices from the Gaifman graph of I' leaves the same kind of
tree as before, with longer rows. So tw(I') <= 3.

For Q', keep one current vertex per string. For each j, first run the k Step
chains one at a time; bags have at most k+1 vertices. Then for t = 1,...,L add
z_(j,t), move every string's current vertex one edge forward, and forget
z_(j,t); bags have at most k+2 vertices. Hence pathwidth(Q') <= k+1.

Q' has O(k ell (N+L)) elements and I' has O(k + L sum_i n_i), both polynomial
in the input length since L <= log_2 of it. Sections 3 to 6 apply unchanged:

    tw(G) <= max(k+1,3),    tw(H) <= 3.

### Consequences

**Theorem.** Graph homomorphism parameterized by the larger of the two
treewidths is W[t]-hard for every t, even when the target has treewidth at
most 3.

This follows from the first cited result, since the reduction runs in
polynomial time and its parameter max(k+1,3) depends on k alone.

**XNLP-hardness.** XNLP-hardness is defined through reductions computable in
space O(g(k) + log n). Every vertex of G and H has an explicit name built
from a bounded number of indices, each polynomially bounded: a string, a
position or step counter, a bit index, a relation and argument position, a
position on a prime cycle, and a gadget coordinate. Whether two named vertices
are adjacent depends on a comparison of such indices and on single input
symbols, where a symbol's code is its rank among the distinct letters. All of
this is computable in logarithmic space. We therefore claim that the reduction
is a parameterized logspace reduction, and that the problem is XNLP-hard. This
paragraph is a proof sketch; it has not been formalised or written out in a
machine model.

**Pathwidth (not worked out).** The source is built from a path decomposition,
and each later stage attaches pieces of bounded size. We expect that the same
argument with path decompositions gives pathwidth k+O(1) for G and O(1) for H.
Together with membership of bounded-pathwidth binary CSP in XNLP (Bodlaender et
al., Theorem 14) that would make homomorphism parameterized by pathwidth
XNLP-complete, with targets of constant pathwidth. We have not checked the
constants and do not claim this.

### Status

Lean checks the combinatorial reduction of this section for every finite
alphabet: decision equivalence, source width at most max(2k,3), target width at
most 3, and a polynomial vertex bound
([`BlockLCS.alphabet_full_reduction`](TreewidthHom/BlockReduction.lean)). As in
the binary case, the source bound k+1, the polynomial-time and logarithmic-space
claims, and the cited hardness theorems are outside Lean. The construction is
also implemented in
[bounded_width_hom_hardness.py](scripts/bounded_width_hom_hardness.py) for any
alphabet. The finite checks of Section 7 compare it with direct enumeration on
3,848 instances over three to eight letters, validate the width bounds k+1 and
3 on each, and run three complete constructions. We have not located this
strengthening in the literature, but our search was limited and we make no
novelty claim.
