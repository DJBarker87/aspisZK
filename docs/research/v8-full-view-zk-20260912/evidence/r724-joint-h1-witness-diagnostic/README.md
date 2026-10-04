# R724 joint H1 witness diagnostic evidence

This directory contains source, inputs, outputs, logs, and receipts for the R724 standalone optimized Rust matrix diagnostics. It has no verifier binaries. The main report is `../../R724_JOINT_H1_WITNESS_DIAGNOSTIC.md`.

`attempts/attempt-a` and `attempts/attempt-b-launch-failure.log` retain initial build/launch failures. `attempt-b2` preserves the fixed-z 241-column run; its runner did not load the full frozen R117 flags. `attempt-c-shifted` is the shifted-z 241-column rank-221 run with raw matrix and independently checked left null vector. `attempt-d-single-column` adds only the identified `(47,3)` direction, compares every old C matrix entry and checks the old covector against the new column, and reaches rank 222. `initial-rejected-matrix-not-run.rs` is retained as an explicitly unrun/rejected draft.

The C and D jobs used selected R117 stage pin `6677d5f1310ff7373301fbd79f186278f772e68a`, full frozen rustflags SHA-256 `df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8`, overflow checks, and the recorded 5G/7G/swap-zero cgroup. Exact per-attempt commands, status, wall time, RSS, swap, and source hashes are in the attempt receipts and manifests.

This is diagnostic finite-field data, not a formal theorem or actual verifier execution. The 23×3 preflight is not the 88 observations at the actual 22 query roots. The algebraic chord parameters `(7,5,-5)` use CM31-subfield inputs rejected by the selected OOD sampler. It does not establish full privacy or security. `#print axioms` is not applicable to these Rust runs.

`SHA256SUMS` covers every regular evidence file except itself.
