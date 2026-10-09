# Selected initial/occupancy source construction

`lean/SelectedInitialOutputsSourcePolynomial.lean` constructs all sixteen
initial semantic coordinates as chronological source polynomials.  It retains
both contributions that the selected callback adds into positions 0 through
11: the initial schedule residual and the transfer occupancy residual.
Positions 12 through 15 retain only the schedule contribution.

The schedule source uses the exact full-initial and rate-initial row sets,
the same-index `z` opening, and the literal domain/length initial-state target.
The occupancy source uses rows 1017 and 1018, exact opening indices 0, 1,
2..10, the inverse relation in index 9, and transfer output expectation one
in position 11.  Local coordinate degree is at most three.  Every Boolean
source table is proved equal to the complete lifted
`SelectedSemanticRows.residual (.initial column)`, including the additive
occupancy term.

The independent array-shaped theorem proves the occupancy index/order/sign
calculation and its addition to the schedule functional equal the source
value.  Equality of the pinned Rust factorised high/low schedule selectors and
constant computation to the schedule functional remains a separate literal
source-refinement seam, as does Rust/Aeneas machine semantics.

This adds sixteen outputs to the prior 69/95, bringing constructed semantic
source coverage to 85/95.  The eight public-digest and two public-scalar
coordinates remain.

The focused Lean 4.32.0 NUC replay exited 0 in 13.03 seconds, used 6,860,312
KiB peak RSS and zero swaps.  All promoted declarations print only `propext`,
`Classical.choice`, and `Quot.sound`.  Exact evidence is under
`results/v8-completion-fs-extraction-20260911/selected-initial-outputs-source-v1/`.
