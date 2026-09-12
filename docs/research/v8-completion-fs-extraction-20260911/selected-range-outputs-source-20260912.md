# Selected range-output source construction

Status: focused Lean proof complete; literal Rust refinement remains open.

`BooleanSuffixSourceAlgebra.lean` proves exact closure of local coordinate
slices under zero, addition, negation, subtraction, fixed scalar
multiplication, finite sums, and products with an explicit degree-sum
premise. The product constructor does not infer that two degree-27 factors
have a degree-27 product.

`SelectedRangeOutputsSourcePolynomial.lean` applies the generic chronological
constructor to all 30 range outputs used by the selected
`add_value_lanes` path: ten `z`, ten `succ_z`, and ten `xor12_z` values under
the shared rows 1008/1010/1012 selector. For every output it proves that the
constructed Boolean table is exactly the lifted literal
`SelectedSemanticRows.residual (.rangeBit bit)` table. It also constructs any
verifier-fixed linear projection of all 30 outputs using the closure layer.

This closes 30 of the 95 selected semantic coordinates at the mathematical
source-polynomial layer. It does not derive off-domain values from equality
on the Boolean cube. It does not yet prove that the pinned Rust opening
arrays and selector implementation produce these mathematical tables; that
literal machine/source refinement is the remaining boundary for this group.

Focused NUC builds used Lean 4.32.0 under a user systemd scope with
`MemoryHigh=9G`, `MemoryMax=10G`, and `MemorySwapMax=0`. Both exited zero and
reported only `propext`, `Classical.choice`, and `Quot.sound`. Exact commands,
hashes, timings, peak RSS, and logs are in:

- `results/v8-completion-fs-extraction-20260911/boolean-suffix-source-algebra-v1/`
- `results/v8-completion-fs-extraction-20260911/selected-range-outputs-source-v1/`

No protocol, proof-body, verifier-acceptance, or probability statement is
changed by this leaf.
