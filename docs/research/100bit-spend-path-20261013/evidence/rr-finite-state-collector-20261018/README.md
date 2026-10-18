# Complete finite child state and a recursive prefix collector

This packet closes the previously explicit omitted-row gap in the coefficient-vector normalization model and proves the recursive prefix program's correctness from its local interfaces. It is not a complete efficient list-decoder instantiation or 100-bit soundness theorem.

## Complete state representation

`RRSubstitutionTailBound` proves every substituted inner-X row above M+ell is zero when input rows through M have outer-Y degree at most ell. It also proves every omitted normalized row is zero when v+k exceeds M+ell. `RRSubstitutionOuterDegreeBound` proves substitution and normalization preserve that same outer-Y degree bound for all rows, so the bound can be used at subsequent recursion steps.

`RRVectorNormalizedRowsV12` proves exact per-row readback for finite row construction followed by list.drop. `RRVectorNormalizedStateV4` gives equality of the whole retained list. `RRVectorNormalizedCompleteV3` handles every index, including indices beyond the finite state's end, where the actual model row is zero. `RRVectorPolynomialReconstructionV9` reconstructs the complete bivariate child from those rows. Slices are embedded using `liftCoeffPolynomial`: the row at inner degree n contributes `C(X^n) * liftCoeffPolynomial(slice_n)`. Treating the slice itself as a bivariate constant would swap the variable roles and is not used.

Thus finite state construction/drop has a complete polynomial readback; it is no longer just a bounded projection that might omit nonzero coefficients. The degree and lower-zero premises are explicit, and the preceding scanner/normalization packet supplies the selected-index/lower-zero facts. No large concrete field elimination or coefficient expansion was executed.

## Recursive program

`RRPrefixCollector.collect` is an executable recursive prefix collector over a state type, an explicit Boolean zero-tail test, and an explicit list-valued child function. Its runtime data contains no Mathlib polynomial, and the definition has no axioms. `collect_complete` proves every root of degree below the selected depth (and the zero polynomial) appears in the returned coefficient vectors when the local child interface contains its head/tail descent and the zero test is exact. `collect_sound` proves every returned vector reads back to a root when the child interface preserves roots. The proof derives the divX degree reduction and coefficient-vector cons identity.

These are checked contracts, not a free proposition named polynomial time. Instantiating them with the concrete vector-state zero test and certified root-list children is the next step. The finite-field root-factor backend, adaptive randomness/failure budget, interpolation construction, full decoder/caller counts and the entire operation-cost proof remain open.

## Evidence

`accepted-targets.json` records seven new accepted owners and exact previously accepted dependencies. Publication checks source and log hashes, standard printed axioms and recursive custom-import object hashes. Each original receipt records its actual source revision, frozen source/object hashes, native pinned Lean 4.32 command, exit status, time, RSS and swaps. All selected targets exit zero; printed proof reports contain only propext, Classical.choice and Quot.sound or subsets; the collector definition reports no axioms. Every process swap count is zero, while existing host swap is recorded separately. No unchanged full replay or production Rust change was performed.
