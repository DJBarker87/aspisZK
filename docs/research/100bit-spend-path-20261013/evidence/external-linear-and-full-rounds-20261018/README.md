# Actual lazy external layer and full-round callers

`PoseidonExternalLinearExact.external_linear_lazy_success` now derives actual source success from canonical input, canonical output, and the existing R0P external-linear model at every one of the sixteen output cells. It composes the actual first matrix loop, ordered raw column sums, and actual second loop. No intermediate caller success is assumed. The second loop invariant correctly uses the matrix-transformed stage as its fixed baseline; the separate first-loop model connects that stage to the original input.

`PoseidonFullRoundLazyExact.m31_source_success` and `qm_source_success` then compose the checked nonlinear loops with that caller, proving the actual M31-constant and QM31-constant lazy full rounds against `R0P.poseidonFullRound`, including output canonicality.

The five new source modules have six standard-only theorem reports. The unchanged first-loop Fuel source was rebuilt under its correct dotted module owner to supply a missing import artifact; its previously proved theorem is not counted as new. No binary was renamed to a different module. Focused source, exact imports/compiler/commands, revision, exit, time, RSS, swap, object hashes and axiom reports are retained for each target in its receipt and log. Jobs were serial with Lean -j1/-M4400 and an aggregate 8GiB monitor; all accepted checks used zero process swap. No package-wide replay or unchanged runtime gate was run.

The selected packed external layer, packed full rounds, complete projected evaluator correspondence, and end-to-end 100-bit security/privacy remain open. These are source-arithmetic proofs, not a completed cryptographic security theorem. Production Rust and deployed artifacts are unchanged.
