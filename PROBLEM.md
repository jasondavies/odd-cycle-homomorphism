# The problem

Given finite simple undirected graphs G and H, decide whether there is a graph
homomorphism `f : V(G) → V(H)`: every edge of G must map to an edge of H. No
injectivity or surjectivity is required. The parameter is the maximum of the
two input treewidths.

Is this problem fixed-parameter tractable, or is it W[1]-hard? The related
conjunctive-query question uses the treewidths of the query and database
Gaifman graphs.

Sources:

- [a3nm: Complexity of query evaluation parameterized by treewidth](https://a3nm.net/work/research/questions/#complexity-of-query-evaluation-parameterized-by-treewidth)
- [Graph-homomorphism formulation on cstheory](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth)

The written solution gives W[1]-hardness even when the target is an odd cycle,
which has treewidth 2, and W[t]-hardness for every t by a chained variant.
It does not establish W[1]-membership or W[1]-completeness. The source width
still depends on the parameter; the result does not assert hardness with both
widths fixed constants.

## Public status and attribution

The source workspace checked the public status on 2026-11-12. The entry was
still on a3nm's main list and the linked question had no posted answer. However,
[Amarilli's May 2025 comment](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth#comment124806_34877)
already announced W[1]-hardness reductions from workshop participants. A public
proof was not located in that check. Lack of a posted answer is not evidence
that the result is unclaimed or new.

This repository preserves our reductions and their formalisation; it does not
claim to be the first resolution. The hardness of Multicoloured Clique and of
Chained Multicoloured Clique is established prior work. Independent assessment
of correctness, overlap with the announced reductions, and publication value
remains outstanding.
