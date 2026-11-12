# Cost-model boundary

**The complete measured constructor now has a checked polynomial bound in an
explicit traversal/comparison model.** Its output is proved equal to the
verified executable constructor. A bit-time or machine-runtime theorem is
still missing: some operations have assigned primitive costs whose physical
implementation has not been formalised.

## Complete constructor

[MeasuredReduction.lean](TreewidthHom/MeasuredReduction.lean) defines
`compileMeasured xs ell q`. It performs preprocessing, constructs both LCS
relational structures, enumerates their facts and incidence vertices, adds
marker cycles, generates sparse arcs, and serializes the direction gadgets.

`compileMeasured_value` proves, for every input and assigned primitive charge
`q`, that the result is exactly `(compile xs ell).data`. Therefore the existing
decision-equivalence, width, and size theorems apply to the graph data it returns.
The measured vertex and arc lists themselves feed serialization; they are not
replaced by separately recomputed ordinary enumerations.

`compileMeasured_polynomial` proves that a single polynomial `p : Polynomial Nat`
satisfies, for every `xs`, `ell`, and `q`,

```
(compileMeasured xs ell q).cost ≤ p.eval (100 + encodedInputSize xs ell + q).
```

Here `encodedInputSize = number_of_words + total_word_length + ell.size + 1`:
words are explicit bit lists, word delimiters have unit size, and the requested
length is binary. The proof uses the very loose composition bounds
`B_0(s)=s+1` and `B_(j+1)(s)=100*(B_j(s)+1)^3`, with a fixed depth of 31.
This is an existence proof of a polynomial bound, not a useful performance
estimate. Do not expand or numerically evaluate that bound in regression tests.

Preprocessing has exact modeled cost
`total_word_length + (q+6)*number_of_words + 1`. It explicitly traverses word
lengths and computes the count, total, and short-word flag in one pass. These
computed results control the branches and supply the padding bound. A requested
length of `2^256` is handled without a loop over its numeric value. Zero words
or zero requested length produce the fixed yes-instance; a short word produces
the fixed no-instance. All other inputs execute the full graph construction.

## Charged operations and primitive boundary

- `MeasuredPreprocessing` charges each visited input/word cell and assigns `q`
  to requested-length comparisons.
- `MeasuredDomains` charges finite-domain generation, sums, products, and
  dependent sums. Each target word lookup plus length operation receives `q`.
- `MeasuredLCS` expands the query and target relation tests into explicit finite
  existential searches. Their atomic equalities, comparisons, and accesses
  receive `q`; Boolean combinations and schema dispatch are charged as well.
- `MeasuredSchema` composes fact filtering, incidence vertices, marker cycles,
  and sparse arc generation. The schema has arity at most two and 18 marker
  types, with marker lengths at most 67.
- `MeasuredRelational` composes these lists with `IndexedAssemblyCost`.
  The serializer charges arc lookup, repeated list-length traversals, endpoint
  searches, finite ranges, and construction of the integer edge list. Its
  assigned base-vertex comparison charge is `q`.

Generic enumeration mapping callbacks still receive a one-step charge. Their
concrete uses include constructor/equivalence maps, bounded tuple operations,
marker lookup, and arc endpoint calculation. Arithmetic is currently unit cost.
Structured equality and word access are assigned `q`; there is no theorem yet
showing that a specific polynomial `q(input_length)` bounds their bit cost.
The extra `q` in the raw constructor covers recovering the input word count.

These are precise definitions of an abstract model, not automatic certificates
for arbitrary Lean expressions. Instrumentation overhead, parsing, and JSON
libraries are outside the model. In particular, equality of the measured and
ordinary outputs does not establish a bound on the ordinary Lean CLI's runtime.

## Serialization bound

For supplied base-vertex and arc lists of lengths `n` and `m`, respectively,
`indexedAssemblyMeasured_cost` proves the bound

```
(m + 60*(q+2)*n + 3094)*m + (m+1)^2 + n + 2*m + 7.
```

If `n,m ≤ b`, this is at most `10000*(q+2)*(b+1)^2`.
`indexedAssemblyMeasured_value` proves output equality with the production
indexed serializer. This stage is now included in the complete bound above.

## Remaining closure

1. Implement and justify primitive equality, arithmetic, marker/tuple operations,
   and word access in an explicit bit-cost or machine model. Prove the necessary
   representation-size invariants and refine the measured program into that
   model. The binary length of `ell` must remain included.
2. Instantiate a parameterized-reduction framework and derive hardness with
   Pietrzak's published binary-LCS hardness theorem explicitly external.

No project axiom asserts these obligations. Output size, execution timings, and
the completed abstract cost composition do not replace them.
