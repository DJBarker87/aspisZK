# WideExact indexed-word extraction attempt f

This isolated candidate starts from attempt e (explicit outer length match) and changes only the inner four-byte conversion to indexed reads from each `chunks_exact(4)` slice. The source still loops over chunks and calls `Self::from_limbs`; the current runtime source was not edited.

With pinned Charon/Aeneas, `--mir built`, no `--monomorphize`, and a 4G/6G/zero-swap/128-task cgroup, Charon extraction succeeded and Aeneas translation exited 2. Aeneas reported markers remaining after context collapse (ended region `{9}`; one frame, locals 40, abstractions 11). This attempt was not retried. The full source pins, candidate patch, LLBC, logs, timings, tool/environment pins, and status are preserved. No successful Lean output or runtime adoption claim is made.
