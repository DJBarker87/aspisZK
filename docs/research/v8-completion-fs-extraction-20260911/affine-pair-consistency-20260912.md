# Optimized affine-pair consistency

`SameBodyAffinePairConsistency.tensorPair_eq_entries` proves that the
shared-product construction used for the affine correction computes exactly
the two literal tensor entries `(0, 2)` in x mode and `(0, 1)` in y mode, for
arbitrary three-row QM31 point tables and row scales.

The proof isolates a one-row ten-coordinate factorisation and closes its two
nontrivial identities with `mul_sub` and commutativity. It adds no semantic,
soundness or honest-input premise. The direct specialisation to the large
prepared source record and dense `originalWeight` exhausted the focused
250,000-heartbeat budget during definitional equality checking; that bridge
is not claimed here and the cap was not raised.

Focused NUC compile used pinned Lean 4.32 and the existing V8/base cache:
exit 0, wall 3.77 seconds, peak RSS 6,770,056 KiB, swap 0. Source SHA-256 was
`70d91b00184622273362579fd2907b2ca793aaee48dd0ff8006339f620f85822` and
OLean SHA-256 was
`1b8f9ddd8d5e6fe241979d929b3849eb6191544b848612e805988597e55903ec`.
The theorem prints only `propext`, `Classical.choice` and `Quot.sound`.

This is functional field algebra, not literal Rust/Aeneas refinement or an
SBF/CU measurement. It changes no protocol or proof bytes.
