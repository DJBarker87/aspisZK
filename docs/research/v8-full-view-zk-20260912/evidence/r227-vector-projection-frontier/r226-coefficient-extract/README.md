# R226 focused coefficient extraction attempt

One authorized extraction attempt using the pinned cached release setup. Charon exited 101; it wrote no LLBC, so declaration IDs, selected method bodies, and reachable opaque obligations could not be inventoried. No alternate selectors or retries were attempted.

The exact failed `--start-from` patterns are preserved in `extract-command.json`. Charon's compiler diagnostics in `extract.log` show that the four patterns were rewritten as `crate::...::{impl crate::...::Coeff}::method` and rejected with: `--start-from only supports impl patterns if they're the first element of the path`. The build reached rustc, demonstrating the release setup was invoked, but this is a selector-shape failure and does not establish whether the intended methods would otherwise be selected.

The command used Charon's `aeneas` preset, built MIR, default sysroot, and four requested starts. It included `crate::circle_norm::{norm,polar,times_r}` individually and `aspis_core::field`; it omitted `--monomorphize`. Cargo used `--offline --locked --release --jobs 1`, features `insecure-spend-fixture,selected-v7-kernels`, and the cached performance-host manifest/bin. Exact argv and rustflags are in `extract-command.json` and `launch.json`.

Frozen snapshot: `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a` (no `.git` metadata). Launch campaign revision recorded from the local worktree: `18f8ecd7ef9731c69211a970698d1aedc872a74b`. Verified SHA-256 inputs are recorded in `result.json` and `extract-command.json`, including circle_norm, line_norm, joined_inverse, aspis_core field, Cargo.toml, and Cargo.lock. Pinned Charon SHA-256 and Rust/Cargo versions are in `toolchain.txt`; cached release rustflags match R207 SHA-256 `f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613`.

The `aspis-r226-coefficient-extract` systemd scope used `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. `extract.log` records 13.34 s wall time, 608608 KiB peak RSS, zero swaps, exit 101. Before/after host reservation and the cgroup settings are recorded in the two reservation JSON files. The runner was based mechanically on `.r21-scratch/r219-norm-leaf-extract/run_extract.py`; this bundle includes the exact adapted runner, launch argv, logs, source excerpt, and SHA256SUMS.

No source, toolchain, or Lean files were edited. No commit was made. No formal or semantic claims are made.
