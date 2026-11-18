# Palomar submission

The proposed registry result is **List elimination into odd-cycle homomorphism
with additive structural bounds**. This title describes the Lean theorem;
the manuscript's complexity classifications remain outside the formal claim.

## Statement and proof

[Challenge.lean](Challenge.lean) is the independent statement a reviewer
can audit. It imports only Mathlib and defines the custom decomposition, width,
feedback vertex number, and degeneracy notions in full. Its single deliberate
proof placeholder is required only for comparison; no definition is unspecified.

[Solution.lean](Solution.lean) proves
`TreewidthHom.Palomar.list_elimination` using the existing development. It chooses
`ListReduction.source` as the finite graph witnessing all the conclusions:

- equivalence between list colourability and ordinary homomorphism to `C_n`;
- treewidth at most `max(tw(F)+2,3)` and pathwidth at most `pw(F)+6`, including
  transfers of supplied decomposition certificates with polynomial bag-count
  bounds in the input bag count, vertex count and numeric target length;
- finite-index output tree certificates even from arbitrary-index input ones;
- target pathwidth at most two;
- transfer of any feedback vertex set to one with exactly two more vertices,
  hence feedback vertex number at most `fvs(F)+2`;
- 2-degeneracy, girth at least `n`, and exact girth for nonempty inputs;
- connectedness when every list omits a residue;
- explicit polynomial vertex and linear edge bounds;
- exact treewidth and feedback-number transfer under a common forbidden last
  coordinate and an input edge, and a pathwidth lower bound for nonempty inputs;
- the target-capping equivalence for the witness graph;
- the target-free odd-cycle-core reduction for nonempty inputs.

The statement is existential to avoid exposing implementation-specific vertex
representations in the review surface. The proof chooses the actual construction,
not an arbitrary encoding. Neither existence nor the cardinality bound asserts
an executable logspace transducer. The library additionally proves target
capping and the shortest-odd-cycle recognition equivalence for arbitrary graphs.
Circular chromatic number, complexity classifications and machine resource
bounds remain outside Lean; see [FORMALIZATION.md](FORMALIZATION.md#outside-lean).

The custom definitions in Challenge have the same names and bodies as their
counterparts in the proof development. Challenge and Solution are compiled
separately; Solution never imports Challenge. Comparator checks their agreement
and that the solution has only the three permitted foundational axioms.

## Reproduce the submission checks

Use a normal checkout with its own dependency cache, Linux, Python 3, elan, and
`bwrap` (bubblewrap). The pinned Lean 4.35.0 bundles Comparator and the independent
kernel checkers. From the repository root:

```sh
lake exe cache get
python3 scripts/check_formalization.py
./scripts/check_palomar.sh
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The ordinary build and axiom audit include Solution but exclude the deliberately
incomplete Challenge. Comparator builds Challenge separately; its one proof-hole
warning is expected. The audit checks 115 proved declarations and scans Solution
for admissions along with the library.

The Comparator script preserves sandboxing and uses the toolchain's bundled
Lean, NanoDa, and con-ron checkers. It generates a temporary protected configuration;
`comparator.json` itself contains only Palomar's accepted submission fields.
A dependency cache symlinked to another checkout may be hidden by Comparator's
sandbox. Use a self-contained checkout rather than disabling sandboxing.

[formalization.yaml](formalization.yaml) records authorship, mathematical sources,
classification, AI assistance, agent-review status, and the verification boundary.
The repository includes the substantive proofs, so this is not a thin wrapper
around an external formalisation. [LICENSE](LICENSE) supplies Apache-2.0 for this
repository; dependencies and cited works retain their own licences.

## Preparation checks (17 November 2026)

The standalone pair passed Comparator with Lean, NanoDa, and con-ron. The check
used an isolated copy with contained dependency caches and sandboxing enabled;
its Lean sources and configuration matched this working tree. The expanded
109-declaration axiom audit and all ten Python regression tests passed.
Palomar's metadata validator accepted `formalization.yaml`, including provenance
and subject classifications. All 42 project Lean files have module headers and
satisfy the source-size limits; the toolchain matches the pinned mathlib release.
These are local checks, not a Palomar submission or registry decision.

## Final snapshot and submission fields

Commit and push the prepared files before submitting. Palomar reviews a public,
immutable commit, excluding all uncommitted changes. Obtain the complete SHA with
`git rev-parse HEAD` after committing. Check that the chosen revision is visible
on GitHub; do not submit an earlier manuscript-only revision.

| Field | Value |
| --- | --- |
| Repository | `https://github.com/jasondavies/odd-cycle-homomorphism` |
| Commit | Full 40-character SHA of the final prepared and pushed commit |
| Project path | Leave blank (repository root) |
| Comparator configuration | Leave blank (`comparator.json`) |
| Formalisation metadata | Leave blank (`formalization.yaml`) |
| Relationship, when Jason Davies submits | Responsible author or maintainer |

Follow [Palomar's submission instructions](https://palomar-registry.org/how-to-submit).
Submitting for review and registering the resulting record are separate actions.
Keep the private status link: it is needed to read the review and choose whether
to register. This preparation does not create a submission or register a result.
