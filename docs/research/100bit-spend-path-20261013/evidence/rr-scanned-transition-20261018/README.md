# The executed first-slice index controls a sound normalized transition

`RRScannedNormalizedTransition.scanned_normalized_transition` composes the actual finite row scanner with the actual affine-substitution polynomial model. Given a nonzero initial coefficient polynomial p and a scan bound L at least its root multiplicity at a, it proves the scanner returns an index v no greater than that multiplicity. The child obtained by coefficientwise stripping at that same returned index has nonzero inner-X=0 specialization, specialization degree at most the parent root multiplicity, and exactly the roots prescribed by affine head/tail descent. The theorem quantifies over every candidate tail polynomial. It has no free factorization premise and does not select a separate existential normalization index in place of the scanner's returned value.

The components are:

- `RRVectorRowNonzeroV5`: the executed row-nonzero Boolean is true exactly when its polynomial readback is nonzero.
- `RRVectorActualScannerV2`: finite scanning of rows 0 through L returns the first nonzero actual fixed-parent slice, with all earlier slices zero and index bounded by root multiplicity.
- `RRNormalizedChildSlice`: specializing the stripped child at inner X=0 gives that exact chosen slice. This connects child normalization to the previously proved degree/mass bounds.
- `RRActualNormalizedTransition`: proves the explicit parent-from-slices affine expansion and combines normalization/root preservation with the selected-slice multiplicity bound.
- `RRScannedNormalizedTransition`: substitutes the executed scanner result into that transition.
- `RRVectorRowEvalV3`: a concrete successful `#eval` of the direct row constructor over ZMod 7, returning `[0, 4, 0]`. Executability is supported by the recorded evaluation, not inferred from the presence or absence of standard axioms in a polymorphic definition.

This is a one-step correctness theorem, not the complete executable decoder. The child's polynomial normalization is still a proof specification. The coefficient-vector state update via finite row construction and list.drop, including the full M+ell truncation bound, is next. Full recursion/completeness, complete root factorization and adaptive randomness, interpolation, implemented caller/site counts, and polynomial operation-cost/failure accounting remain open. This packet does not close 100-bit soundness or production source correspondence.

`accepted-targets.json` identifies six new accepted module owners and exact dependencies reused from `rr-decoder-descent-20261018`. Sources and logs are hash-checked; custom imports match their accepted object hashes. Each receipt retains its actual source revision, exact source hash, native pinned Lean 4.32 compiler, command, exit status, wall time, RSS, swaps and axiom report. All accepted targets exit zero; every printed report contains only standard axioms. Process swap counts are zero; recorded existing host swap is separate. No unchanged full replay, production change or large numeric calculation was run.
