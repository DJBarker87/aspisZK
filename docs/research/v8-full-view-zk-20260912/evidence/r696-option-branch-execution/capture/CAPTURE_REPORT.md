# Selected owned-fold Option wrapper capture

This is a source-capture result only. It does not establish source-to-model semantics or close a formal security claim.

The single approved Charon job completed successfully under its own systemd cgroup. It used the frozen R117 source snapshot at revision `6677d5f1310ff7373301fbd79f186278f772e68a`, the existing selected full Rust flags, offline/locked release Cargo settings, and three additional exact Option includes: `Option::unwrap_or_else`, `Option::branch` for `Option<T>`, and `Option::from_residual` for `Option<Infallible>`. The capture began at `crate::r17_host_relation::owned_primal::fold`; no source, harness, LLBC, Aeneas input, or compiler was changed.

The resulting LLBC has `has_errors=false`; it contains 271 function declarations, 67 type declarations, 20 globals, 31 trait declarations, 60 trait implementations, and 173 ordered declarations. Its SHA-256 is `090797a384c3ecefcc28b03ec4b61f0796804bf68326a7044c61aa2e9b217a2a`.

All three requested declarations are present. `Option::branch` (FunDecl 127) and `Option::from_residual` (FunDecl 128) have structured bodies. The captured `branch` body matches the Option discriminant and returns the corresponding ControlFlow variant; `from_residual` checks the residual discriminant before constructing `None`, preserving its assert/error path. `Option::unwrap_or_else` (FunDecl 11) is `Foreign`/`Opaque` in this LLBC, so this capture did not expose its implementation body. This is the next source/library frontier for the owned-fold closure. No Aeneas translation was started; the lead must inspect the capture first.

Exact argv, Rust flags hash, source hashes, cgroup reservation, logs, timing, and complete result metadata are retained alongside this report in `capture-command.json`, `launch.json`, `launch-exit.txt`, `ssh-launch.log`, `charon.stdout.log`, `charon.stderr.log`, `charon.time.log`, `result.json`, and `receipt.json`. Formal axioms are not applicable to a source capture.

The local launcher was invoked as `python3 run_capture.py --help`; this copied runner does not parse command-line arguments and launches unconditionally, so the extra flag did not alter the approved Charon argv. The exact launcher snapshot used at execution (`run_capture.launched.py`) is retained separately from the corrected retrieval helper (`run_capture.py`). The launcher completed the remote job; its original post-run fetch referenced the prior LLBC filename, so I retrieved the already-produced new filename directly without rerunning capture.
