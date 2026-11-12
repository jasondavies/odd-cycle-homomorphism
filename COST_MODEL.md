# Cost-model boundary

The verified executable constructor is complete. **The polynomial running-time
proof for the entire constructor is not complete.** The current cost library
proves properties of explicit instrumented traversals; it does not certify the
running time of arbitrary Lean code or of the CLI.

## Completed serialization theorem

`indexedAssemblyMeasured` in
[IndexedAssemblyCost.lean](TreewidthHom/IndexedAssemblyCost.lean) executes sparse
integer numbering and edge generation from supplied lists of base vertices and
arcs. `indexedAssemblyMeasured_value` proves that its output is exactly
`indexedAssembly.data`, the encoding used by the verified constructor.

Write `n` for the base-list length, `m` for the arc-list length, and `q` for the
cost assigned to one base-vertex equality comparison. The checked bound is

```
(m + 60*(q+2)*n + 3094)*m + (m+1)^2 + n + 2*m + 7.
```

If both lists have length at most `b`, the bound is at most
`10000*(q+2)*(b+1)^2`. In particular, `b` can be the final graph order `n+11m`.
This is a quadratic traversal/comparison-model bound for this stage, with the
equality cost explicit. It is not yet a polynomial bit-time theorem for LCS
reduction.

The model charges for visited cells in list lookup and length computation,
base-vertex searches, finite-range generation, mapping, concatenation, and
output construction. The instrumented finite-range routine explicitly visits
and shifts its existing indices, yielding the checked `(m+1)^2` bound. The
serializer pays for each arc lookup and repeated base-list length computation;
preparing the supplied lists is outside this stage. Fixed-size gadget-coordinate
operations are primitives of constant cost, and arithmetic currently has unit
cost. Instrumentation overhead itself is not included in the modeled cost.

## Generic components

- `SerializationCost` checks linear search and a simple general endpoint
  serializer. The production constructor uses the faster indexed serializer.
- `MeasuredLists` checks explicitly recursive list operations and their costs.
- `MeasuredEnumeration` connects instrumented enumerators to their ordinary
  enumerations. Mapping callbacks are treated as supplied one-step primitives;
  their internal computation is not certified by the generic map theorem.
- `EnumerationBounds` supplies composition bounds and proves that any fixed
  number of iterations of its bound is polynomial.
- `MeasuredDecision` checks exhaustive finite existential tests with explicit
  costs for their supplied atomic predicates.

These theorems are genuine checked statements about the given algorithms and
counters. Their generic callback contracts must be instantiated and justified;
placing an expensive computation inside `Measured.step` would not prove that
it runs in one physical step.

## Work still needed for full closure

1. Instantiate the instrumented enumerators and finite decisions for the full
   LCS front end, typed incidence, and marker cycles, including preprocessing.
   Prove that the resulting full measured program returns `compile`'s output.
2. Compose their costs with the checked sparse serializer into one polynomial
   bound in the encoded input length. No complete cost theorem is present yet.
3. Establish costs of equality, arithmetic, marker lookup, bounded tuple
   operations, and word access in an explicit bit-cost or machine model. Include
   the bit length of the requested subsequence length; it may be huge even
   when preprocessing immediately rejects it.
4. Instantiate a parameterized-reduction framework and derive hardness with
   Pietrzak's published binary-LCS hardness theorem explicitly external.

No project axiom asserts any of these remaining obligations. They must not be
inferred from the finite execution timings or from the output-size theorem.
