# Homomorphism into an odd cycle is W[1]-hard

**Status, 2026-11-16.** The reduction is checked in Lean: decision equivalence,
both width bounds and polynomial size
([`OddCycle.reduction_cycleGraph`](TreewidthHom/OddCycleReduction.lean)). As
elsewhere in this repository, the hardness of the starting problem, the
polynomial running time and the W[1]-hardness conclusion itself are not Lean
theorems. Not independently reviewed. We have not found this statement in the
literature, but our search was short and we make no novelty or priority claim.
This is a second, independent route to the hardness result of
[SOLUTION.md](SOLUTION.md); it does not use that construction.

## Statement

For an odd number n, let C_n be the cycle on Z_n, with x adjacent to x+1.

**Theorem.** Deciding whether a graph G has a homomorphism to C_n, with G and
the odd number n given as input (n in unary), is W[1]-hard parameterized by the
feedback vertex number of G. It is therefore W[1]-hard parameterized by the
treewidth or the pathwidth of G.

The target has treewidth 2 and pathwidth 2. So graph homomorphism
parameterized by both treewidths is W[1]-hard even when the target has
treewidth 2. This is optimal on the target side: a target of treewidth 1 is a
forest, and homomorphism into a forest is polynomial (it asks whether the
source is bipartite, or edgeless).

The reduction is from Multicoloured Clique with k classes and produces a source
with a feedback vertex set of k+1 vertices. Since Multicoloured Clique has no
f(k) N^{o(k)} algorithm under ETH, neither does this problem have an
f(w) m^{o(w)} algorithm, for w the feedback vertex number, treewidth or
pathwidth of G and m the input size. The standard dynamic programme runs in
time n^{O(w)} m.

## Two facts about odd cycles

**Fact 1 (dials).** Every homomorphism C_n → C_n has the form a ↦ r + εa with
r in Z_n and ε in {1,-1}.

*Proof.* The image of the cycle is a closed walk of length n in C_n. If it
makes s steps backward and n-s steps forward, its net displacement n-2s is a
multiple of n. As n-2s is odd and lies between -n and n, it equals n or -n.
So all steps go the same way. ∎

**Fact 2 (difference paths).** For x,y in Z_n there is a walk of length n-2
from x to y in C_n if and only if x ≠ y.

*Proof.* A walk of length t with s backward steps ends at x + t - 2s. For
t = n-2 and s = 0,...,n-2 the displacements are the odd integers from -(n-2)
to n-2. Modulo n the positive ones are 1,3,...,n-2 and the negative ones are
the even residues 2,4,...,n-1. These are exactly the nonzero residues. ∎

So a path of length n-2 between two source vertices, with new internal
vertices, forces exactly that the two vertices get different images. Call such
a path a *link* between them.

## The reduction

Let Γ be a graph whose vertex set is partitioned into classes V_1,...,V_k, each
with exactly N vertices v_(i,1),...,v_(i,N). (Pad with isolated vertices.) We
ask for a clique with one vertex in each class.

**Numbers.** Let Q = 2Nk+1 and give class i the weight p_i = Q+i-1, so that
Q ≤ p_i < Q+k. Give v_(i,a) the label λ(v_(i,a)) = a p_i. Let
M = N(Q+k)+2 and n = 2M+1. All labels lie in {1,...,M-2}. Put
Λ_i = {a p_i : 1 ≤ a ≤ N} and, for i < j,

    D_ij = { λ(v) - λ(u) mod n : u in V_i, v in V_j, uv an edge of Γ }.

**The source graph G.**

- *Dials.* Take k+1 disjoint copies F_0,...,F_k of C_n. Write f^i_a for the
  vertex a of F_i, and h_i = f^i_0 for its *hub*.
- *Class links.* For 1 ≤ i ≤ k and every d in Z_n outside Λ_i, add a link
  between f^0_d and h_i.
- *Edge links.* For 1 ≤ i < j ≤ k and every d in Z_n outside D_ij, add a link
  between f^i_d and h_j.

The target is C_n. G has at most (k+1)^2 n^2 vertices, and n = O(N^2 k), so
everything is polynomial in N and k.

## Correctness

**A clique gives a homomorphism.** Let v_1,...,v_k be a clique with v_i in V_i.
Map f^0_a to a and f^i_a to λ(v_i) + a. Every dial is mapped by a rotation.
A class link joins f^0_d ↦ d and h_i ↦ λ(v_i), where d is not in Λ_i, so the
two images differ. An edge link joins f^i_d ↦ λ(v_i) + d and h_j ↦ λ(v_j),
where d is not in D_ij. As v_i v_j is an edge, λ(v_j) - λ(v_i) is in D_ij, so
again the images differ. By Fact 2 every link can be mapped.

**A homomorphism gives a clique.** Let φ : G → C_n. By Fact 1,
φ(f^i_a) = r_i + ε_i a. Composing φ with an automorphism of C_n we may assume
r_0 = 0 and ε_0 = 1.

The class links give r_i ≠ d for every d outside Λ_i. So r_i = a_i p_i for some
1 ≤ a_i ≤ N. Let v_i = v_(i,a_i).

Fix i < j. The edge links give r_i + ε_i d ≠ r_j for every d outside D_ij, so
ε_i (r_j - r_i) lies in D_ij. Hence there is an edge between u = v_(i,a) and
v = v_(j,b) with

    ε_i (a_j p_j - a_i p_i) ≡ b p_j - a p_i   (mod n).

Both sides are integers of absolute value at most M, and n > 2M, so this is an
equality of integers. We use one arithmetic fact.

*Claim.* Let i ≠ j and let x,y be integers with x p_j = y p_i. If
|y(i-1) - x(j-1)| < Q, then x = y = 0.

*Proof.* Writing p_i = Q+i-1, the equation says (x-y) Q = y(i-1) - x(j-1). The
right side has absolute value less than Q, so x = y. Then x(j-i) = 0, so
x = 0. ∎

- If ε_i = 1, then (a_j - b) p_j = (a_i - a) p_i. Here x = a_j - b and
  y = a_i - a have absolute value less than N, so |y(i-1) - x(j-1)| < 2Nk < Q.
  By the claim a_j = b and a_i = a. Thus v_i v_j is the edge uv.
- If ε_i = -1, then (a_j + b) p_j = (a_i + a) p_i. Here x = a_j + b and
  y = a_i + a lie between 2 and 2N, so y(i-1) and x(j-1) both lie between 0
  and 2Nk, and their difference has absolute value less than Q. The claim
  gives x = 0, which is impossible.

So v_1,...,v_k is a clique. ∎

## Width of the source

Delete the k+1 vertices f^0_0, h_1,...,h_k. Each dial becomes a path. Every
link has one end at a hub h_j, which is deleted, so it becomes a path hanging
from one dial vertex by its other end, or a separate path if both ends were
hubs. What remains is a forest. Hence G has feedback vertex number at most
k+1 and treewidth at most k+2.

Every tree of that forest is a path with pendant paths, which has pathwidth at
most 2. Adding the deleted vertices to every bag gives pathwidth at most k+3.

## Remarks

- The reduction uses nothing but cycles and paths. There are no relations,
  colours, directions or auxiliary rigid gadgets.
- The numbers only need two properties: for each pair of classes the map
  (u,v) ↦ λ(v) - λ(u) is injective, and no difference equals the negative of
  another. Any labelling with these properties and polynomial range works;
  multiples of distinct primes greater than 2N are another choice.
- A hard target must be triangle-free and non-bipartite once it has treewidth
  2, because a triangle would make it equivalent to K_3. Odd cycles of length
  at least 5 are the simplest such graphs.
- The earlier construction in [SOLUTION.md](SOLUTION.md) gives target
  treewidth 3 but also covers LCS over arbitrary alphabets, and with it
  W[t]-hardness for every t. We have not examined whether the odd-cycle route
  gives more than W[1]-hardness.
- A related published result: periodic timetabling, which asks for values
  modulo T with interval constraints on differences, is W[1]-hard
  parameterized by treewidth (Lindner and Reisch,
  [J. Scheduling 25 (2022) 157–176](https://link.springer.com/10.1007/s10951-021-00719-1)).
  Homomorphism into C_n is the special case where every constraint is
  "difference ±1", so that result does not imply this one.

## Lean

| File | Principal result | Meaning |
| --- | --- | --- |
| [OddCycleTarget.lean](TreewidthHom/OddCycleTarget.lean) | `dial`, `walk_iff_ne`, `cyc_eq_cycleGraph` | Facts 1 and 2. The target `cyc n` is mathlib's `cycleGraph n`. |
| [Links.lean](TreewidthHom/Links.lean) | `linked_hom_iff` | A homomorphism out of a graph with attached paths is a homomorphism of the base graph with a walk of the right length for every path. |
| [ApexForest.lean](TreewidthHom/ApexForest.lean) | `hasWidth_of_apex_forest` | Hubs whose removal leaves parent pointers covering every edge: width at most the number of hubs plus one. |
| [OddCycleReduction.lean](TreewidthHom/OddCycleReduction.lean) | `label_solve`, `source_hom_iff_clique`, `source_width`, `target_width`, `reduction_cycleGraph` | The arithmetic claim, decision equivalence, width at most k+2 for the source and 2 for the cycle, and at most (k+1)^2 n^2 source vertices. |

The input is a graph on `Fin k × Fin N`, and `MulticolouredClique` asks for a
choice of one vertex per class that is pairwise adjacent. The statement holds
for all k and N, including zero. The width bounds use the repository's
tree-decomposition certificates (`HasWidth`). The pathwidth bound k+3 and the
feedback-vertex-set formulation are not stated in Lean; the width proof does
delete exactly the k+1 hubs. All declarations pass the axiom audit with only
`propext`, `Classical.choice` and `Quot.sound`.

## Finite checks

[odd_cycle_hom_hardness.py](scripts/odd_cycle_hom_hardness.py) builds G and
decides G → C_n with a complete search that knows only the graph: arc
consistency with backtracking on the dial vertices, after checking that they
form a feedback vertex set. Once those are assigned the rest is a forest, where
arc consistency is exact. Every homomorphism found is re-verified edge by edge.

[run_odd_cycle_checks.py](scripts/run_odd_cycle_checks.py) compares the answer
with direct clique search on 4,382 instances, 1,798 of them without a clique:

- all 16 instances with two classes of two vertices;
- all 4,096 instances with three classes of two vertices;
- 150 random instances with four classes of two vertices;
- 120 random instances with three classes of three vertices.

It also checks, on every instance, that deleting the k+1 named vertices leaves
a forest, and checks Fact 2 for all odd n from 5 to 39. The search explores
both orientations of every dial. Results are recorded in
[sources/odd-cycle-results.json](sources/odd-cycle-results.json). These checks
supplement the proof; they are not a proof.
