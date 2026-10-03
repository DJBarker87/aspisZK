# R427 evidence boundary draft

Status: proposed checklist only. This note is scratch documentation, not an evidence publication or release decision.

The R427 direct build compiled the instrumented Charon driver with the pinned nightly compiler and saved its output hash. It did not run Charon, extract or print raw MIR, translate LLBC, or compile Lean. The next diagnostic remains pending. The successful compile therefore establishes only that this specific driver source and selected cached inputs produced a binary under the recorded command. It does not explain the origin or semantics of the mutable receiver `Copy(Local 1)` in the saved ULLBC.

The saved build receipt records exit 0, GNU time 0:14.34, peak RSS 1598256 KiB, zero swaps, cgroup peak 2084950016 bytes, and no OOM event. Limits were MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0 and TasksMax 128. The worker reports unchanged inputs: the complete 1,169-entry tracked source tree, all 46 selected extern artifacts, both native PSM files, and all 504 files in `release/deps`. No Cargo invocation or dependency build occurred. Source revision was `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`; pinned rustc commit was `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`; the observer driver SHA-256 is `a7911f86aa775e99e685cc7d1c09e894e6e30c07dc65e83dd21ac0555ef08318`. The custom `get_mir.rs` hook SHA-256 is `246d1fec2223d8ad5755e4aa9f24e647af7c16a18a8a2d893d9085213bf8a9ab`.

R426 remains a separate compiler/frontend diagnostic. Its saved `--print-original-ullbc` output already contains `next(copy self)`. The existing R426 note says that the ULLBC capture does not identify which MIR transformation produced that operand. It also records only a narrowly justified keyed-map comparison for `short_names`; all other serialized AST fields were compared exactly. Keep that scope statement intact when referencing R426.

## Checklist for any later evidence package

- Preserve R426's complete note, source files, ULLBC, raw comparison failure, corrected keyed-map audit, and receipts with their original status labels.
- For R427, include the original launch argv/status, source and toolchain pins, input selection, cache manifest, complete before/after snapshots, rustc logs, both GNU time files, cgroup samples, memory events, and output hash. Keep earlier failed clone/Cargo attempts under history and distinguish them from this direct build.
- Record the binary path and SHA-256 without copying the large binary or cache into the evidence bundle unless a later bounded task explicitly requires it.
- Treat raw MIR observation as a separate, pending artifact. If produced later, record its exact command, source revision, input hashes, output hash, exit status, wall time, peak RSS, swap, and cgroup limits; do not infer semantics from the successful binary build alone.
- Mark `#print axioms` as not applicable to these compiler-only jobs. No Lean target was compiled.

## Failed attempts retained

The first clone attempt failed because its guard incorrectly rejected three tracked symlinks. The corrected clone succeeded. The first cached Cargo build hit a stale zero-symlink assertion before Cargo; a later capped Cargo attempt began compiling `proc-macro2` unexpectedly and was stopped with exit `-15`, 538,214,400-byte cgroup peak, and zero swap. The cache mismatch remains unresolved. Those failures remain historical records; the later direct rustc build is not represented as proof of Cargo-profile equivalence.

No source semantics, ownership, mutable-borrow, callback, privacy, soundness, or cryptographic-security claim is made here.
