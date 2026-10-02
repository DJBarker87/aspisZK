# R387 focused `reduce_u62` extraction preparation

Prepared one cached release Charon extraction with the single selector `aspis_core::field::M31::reduce_u62`, reusing R281's frozen R117 source root, Cargo manifest/lock, release cache, verified rustflags, includes, toolchain and execution limits. No extraction or build was launched.

The frozen `crates/aspis-core/src/field.rs` SHA is `639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499`; the public inherent method is at line 103 and its body at lines 104–105 asserts the `<2^62` bound and calls private `reduce_u64`. The Charon selector is a candidate based on source visibility and R281's associated-method selector shape, not a verified extraction result.

A read-only remote check confirmed field/Cargo hashes match R281, all 28 release fingerprint entries share flags (SHA `f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613`), and the Charon binary hash is `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`. The new output root was absent. Frozen source root has no Git metadata. The launch runner captures active-worktree HEAD when invoked and rechecks source hashes and fingerprint flags before execution.

Prepared systemd unit `aspis-r387-reduce-u62-extract`: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Cargo remains `--offline --locked --release --jobs 1`, with R281 features and no monomorphization. If later authorized, acceptance requires `has_errors=false` and exactly one external (`is_local=false`) Structured body matched to `field.rs:103`; otherwise the runner stops for review. No range premise or source-to-model correspondence is established here.

Lead reviewed the runner and requested two corrections before launch: record the root locality as `is_local=false` (it is an external `aspis_core` function), and assert exact Charon/Rust/Cargo identities. The previous runner is preserved as `run_extract-pre-lead-review.py` (SHA `b4b3b302c785001db2380aca297c4e08ab9dd7aaffef91dfd838d24d7f5de955`); current runner contains those checks and is syntax-checked.
