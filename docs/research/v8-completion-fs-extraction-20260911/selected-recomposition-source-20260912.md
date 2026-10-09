# Selected recomposition source

Status: focused Lean proof complete; literal Rust execution refinement remains
open.

`SelectedRecompositionSourcePolynomial.lean` models the pinned
`reconstruct_10` order exactly: bit 9 is the initial accumulator, then bits
8 through 0 are consumed in reverse order by `acc + acc + bit`. It proves
that this is the little-endian sum

`sum bit[i] * 2^i`.

The three actual views are then combined with scales 1, `2^10`, and `2^20`,
matching the current/successor/XOR12 order in `add_value_lanes`. The proof
relates this literal reverse-Horner expression to a linear combination of
the same committed-table MLE openings, constructs its exact coordinate
slice, proves degree at most one for the reconstruction and degree at most
two after the shared value selector, and packages the result through the
generic chronological Boolean-suffix constructor.

For every Boolean row, the constructed source table is proved equal to the
lifted literal `SelectedSemanticRows.residual .recomposition` value. This is
an off-domain source construction, not an inference from Boolean-table
equality.

Together with the prior range and value/auxiliary leaves, 36 of 95 selected
semantic coordinates now have this mathematical source-polynomial bridge.
The remaining machine boundary is to refine the pinned Rust array indexing,
slice reversal/fold, selector values, and `mul_m31` constants to the field
expression proved here.

The focused NUC build used Lean 4.32.0 inside a user systemd scope with
`MemoryHigh=9G`, `MemoryMax=10G`, and `MemorySwapMax=0`. It exited zero in
12.68 seconds, used 7,573,124 KiB peak RSS, reported zero swaps, and used only
`propext`, `Classical.choice`, and `Quot.sound`. Exact hashes and the complete
log are in
`results/v8-completion-fs-extraction-20260911/selected-recomposition-source-v1/`.

No callback acceptance, protocol, proof bytes, or probability statement is
changed by this leaf.
