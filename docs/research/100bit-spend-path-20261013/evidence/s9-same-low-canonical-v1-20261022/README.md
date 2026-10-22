# S9 same-call low-output canonicality

This packet proves `active_body_scalar_low_canonical` for one successful selected S9 active-body model execution. It consumes the exact `kpowers` array and `scalar_factor` result exposed by `active_body_scalar_prefix`, derives canonicality for the same `kpowers` reads, and follows the same four scalar callback transitions to the pre-quarter accumulator. The final `mul_m31` success is the actual operation returning the selected low value, so the result establishes canonicality of that same output.

The proof uses Lean 4.32.0. It exited successfully in 18.709 seconds with 3,268,919,296 bytes peak process RSS and zero process swaps. The named theorem reports only `[propext, Classical.choice, Quot.sound]`. Import-header preflight covered 5,140 modules with no missing imports. The exact command, profile, source pins, raw Lean log, receipt, and `/usr/bin/time -l` output are retained in `evidence/`.

This is a source-shaped Aeneas/P6 model theorem. It does not prove the frozen Rust `core::array::from_fn` implementation refines the selected model, full helper totality for arbitrary inputs, or global frozen-source S9 closure. The packet contains no `.olean` binaries; the producer object path and hash are recorded in `manifest.json`.
