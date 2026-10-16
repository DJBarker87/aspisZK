# Checked source Horner loop and basis branches

The actual extracted selected-mask reverse Horner loop now has a checked
symbolic execution theorem on Lean 4.32. Starting at zero with end n<=27,
it processes coefficients n-1 through zero, multiplying the accumulator by
the prepared linear value before adding each coefficient. The theorem carries
explicit canonicality requirements and the constructor-derived PreparedFor
invariant. It proves successful execution, canonical output and equality to
the symbolic recurrence. No concrete 26-step unfolding is used.

The actual caller uses end=26 and seeds the accumulator with coefficient 26.
The caller read/range connection, coefficient population and canonicality,
selected linear forms and explicit-mask term are still required to compose
the full selected-mask theorem. The recurrence-to-polynomial bridge is a
separate check; this checkpoint does not assume it.

The source's four tower-basis branches also have checked successful execution,
canonicality and word-map results for canonical inputs and coordinate<4.
These use checked negation and CM31 i/r operations. Exact-field basis decoding
and whole coefficient-array population are subsequent obligations.

The [evidence](../evidence/current-mask-loop-basis-20261016/README.md) contains
six successful targets, thirteen standard-only axiom reports, source/import/
object pins and independent review. Peak target RSS is 2,994,944 KiB and all
process swaps are zero. The five failed proof-plumbing attempts are preserved
separately. Existing reverse-range, array-read and loop-induction proofs were
reused with the actual current Aeneas runtime. No production Rust or measured
artifact changed. The full 100-bit accepted-spend and privacy claims remain
open.
