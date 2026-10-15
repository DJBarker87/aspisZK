# WideExact extraction candidate e

This is an isolated extraction attempt using the current runtime `WideExact::from_le_bytes` loop and only the two explicitly matched `try_into` errors. The original runtime source remains unchanged; current full source pins are recorded in `manifest.json`. The input was copied from the previously pinned extraction kit into this new directory, and earlier sealed attempt bundles were not edited.

With Charon/Aeneas pinned, `--mir built`, no `--monomorphize`, and a 4G/6G/zero-swap/128-task cgroup, Charon extraction completed (exit 0), while Aeneas translation returned exit 2. Its error states that markers remained after context collapse (ended regions `{9, 12}`), with the backtrace through `InterpLoopsFixedPoint.join_ctxs`. The parser still has the same `chunks_exact(4)` loop and `from_limbs` call. No successful Lean output was produced; no retry or source adjustment was made.

`candidate.patch`, copied input sources and pins, the LLBC, full translator output, commands, timing logs, tool/environment pins, and cgroup result are preserved. This is an extraction result only and makes no runtime refinement or adoption claim.
