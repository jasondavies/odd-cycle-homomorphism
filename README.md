# Homomorphism to an odd cycle

A single reduction from List Coloring establishes the complexity of ordinary
graph homomorphism into an odd cycle whose length is part of the input:

| Source parameter | Result |
| --- | --- |
| Width of a supplied path decomposition | XNLP-complete |
| Width of a supplied tree decomposition | XALP-complete |
| Feedback vertex number | W[3]-hard |

Every target has treewidth and pathwidth exactly 2. The construction also gives
2-degenerate sources of arbitrarily large prescribed constant girth.

[Read the paper](paper/odd-cycle-homomorphism.pdf) ·
[Construction and proof](ODD_CYCLE.md) ·
[Formalization boundary](FORMALIZATION.md) ·
[Original question and attribution](PROBLEM.md)

## Lean certificate

The principal theorem is
[`OddCycle.ListReduction.reduction`](TreewidthHom/ListTheorem.lean).
For a List Coloring instance on `F`, with target length `n` odd and at least 5,
it proves:

- decision equivalence with homomorphism `G → C_n`;
- source treewidth at most `max(w+2, 4)` from an input width bound `w`;
- source pathwidth at most `p+6` from an input pathwidth bound `p`;
- target pathwidth at most 2;
- a feedback vertex set of size `|S|+2` from any feedback vertex set `S` of `F`;
- polynomial source size.

Lean also proves the bag-assignment gluing lemma used by the membership
arguments. Published List Coloring hardness, machine time and space bounds,
complexity-class conclusions, degeneracy and girth are **not Lean theorems**.
The paper proves the remaining construction and resource claims in prose.
Completeness uses supplied decompositions; membership without them is not claimed.

## Reproduce

Lean **4.35.0** and mathlib **v4.35.0** are pinned, including dependency revisions.
Requires elan, Python 3, and (for the paper) latexmk with a LaTeX installation.

```sh
lake exe cache get
python3 scripts/check_formalization.py
python3 scripts/run_list_cycle_checks.py
make -C paper
```

The formalization check builds the library, rejects proof admissions and audits
34 declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur.
The executable checks cover 837 finite instances, including 445 negative cases;
finite checks are not proofs. Reports are in [sources](sources/).

## Attribution and history

W[1]-hardness for the original two-treewidth parameter was already announced in
[Amarilli's May 2025 comment](https://cstheory.stackexchange.com/questions/34877/complexity-of-the-homomorphism-problem-parameterized-by-treewidth#comment124806_34877).
Overlap with that work and novelty have not been established. This repository
makes no priority claim. Development and manuscript drafting used AI assistance;
independent review remains pending.

The superseded clique and chained-clique reductions, arithmetic labels, old
checks and manuscript remain in git history at `c88dabb`. The earlier LCS
pipeline remains at `4dfb72e`. The current tree keeps the List Coloring
construction and its supporting lemmas.
