# Optimized affine-pair consistency

`SameBodyAffinePairConsistency.tensorPair_eq_entries` proves that the
shared-product construction used for the affine correction computes exactly
the two literal tensor entries `(0, 2)` in x mode and `(0, 1)` in y mode, for
arbitrary three-row QM31 point tables and row scales.

The proof isolates a one-row ten-coordinate factorisation and closes its two
nontrivial identities with `mul_sub` and commutativity. It adds no semantic,
soundness or honest-input premise. A direct monolithic specialisation first
exhausted the focused heartbeat budget. The retained proof instead uses named
arithmetic projections, constructed prepared-scale equality and the proved
small-index inactive bits to establish `pair_eq_originalWeight` without
raising the cap.

Focused NUC compile used pinned Lean 4.32 and the existing V8/base cache:
exit 0, wall 4.49 seconds, peak RSS 6,774,656 KiB, swap 0. Source SHA-256 was
`856f2decf1e4a74ac250eb4b53a120530a09947d1cf0c5c0c14644c23eb3471a` and
OLean SHA-256 was
`50a6d9836201a2806c6f6b6deb8e1a010f08b6d59a95d911de6b447034c0fdc9`.
The theorem prints only `propext`, `Classical.choice` and `Quot.sound`.

This is source-shaped functional field algebra, not literal Rust/Aeneas
refinement or an SBF/CU measurement. It changes no protocol or proof bytes.
