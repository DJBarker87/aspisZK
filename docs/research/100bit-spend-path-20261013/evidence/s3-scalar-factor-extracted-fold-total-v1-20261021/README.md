# Scalar-factor totality with extracted fold

This packet composes the green constructive scalar-factor totality result with the checked transparent `Iterator::fold` default loop. The exact installer order is `installActualFactorOps (installExtractedFold ops)`; the imported theorem derives the P6 range-fold law for that installed record, and the consumer then proves scalar-factor returns successfully without an independent fold-law or execution-success premise.

The remaining input assumptions are canonicality for every successful in-range read from the caller-supplied `p` and `f` arrays. This does not prove the enclosing Rust `Weights::pair` branch/call-site, caller array assignments, Rust `from_fn` correspondence, or a broader Std model beyond the pinned selected fold source.

The focused target ran with Lean 4.32 arm64, `-j1 -M4400`, exit 0, 4.31 seconds, peak RSS 3,221,864,448 bytes, swap 0, and standard axioms `[propext, Classical.choice, Quot.sound]`. Exact argv, `LEAN_PATH`, and launch revision are retained in `receipts/launch.json`.
