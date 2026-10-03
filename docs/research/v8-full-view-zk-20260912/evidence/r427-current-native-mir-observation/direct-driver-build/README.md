# R427 direct driver build preparation

This is a launch-gated plan only. No remote command, rustc invocation, or compilation was run by this preparation. Root owns launch approval.

The proposed job compiles only `charon/src/bin/charon-driver/main.rs` with the selected pinned nightly rustc and 46 exact cached externs. It binds the required two native `psm` outputs and snapshots all 504 regular files in `release/deps` before and after. The source tree is checked against the saved 1,169-entry clone inventory, including symlink target bytes.

The expected work is a single optimized driver compile, code generation, and link. The job is capped at MemoryHigh 5 GiB, MemoryMax 7 GiB, zero swap, and 128 tasks; it stops after ten minutes or a new cgroup OOM event. GNU time is the parent of rustup/rustc so child cancellation does not discard its accounting. The worker records result/logs before enforcing post-build hash checks.

The compile is explicitly not represented as a reconstruction of the historical Cargo invocation/profile. It launches no Cargo and compiles no dependency.

`run_direct_driver_remote.py` passes `python3 -m py_compile`. No output binary or successful build receipt exists.
