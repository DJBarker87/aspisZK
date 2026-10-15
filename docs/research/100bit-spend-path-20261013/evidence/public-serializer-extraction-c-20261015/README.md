# Public serializer extraction attempt c

This sibling bundle preserves the Aeneas-only `-loops-to-rec` attempt on the exact LLBC saved from attempt b. The parent LLBC is linked at `../public-serializer-extraction-20261015/attempt-b/PublicSerializer.llbc`; its SHA-256 is `4bc765cb58336cee6c3c5a702e14622c285aabf267656ccb6e0e7665169f307c`. The c output contains an identical LLBC copy and verifies the pinned Aeneas binary (`e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813`) and runner (`fbf166decfb66f837e871edaa18befffc32ec7199ec625077bed33c5f7f22c1c`).

Aeneas again exited 2 with `Unreachable` at `lib.rs:239:12-243:9`, through `InterpAbs.merge_abs_conts_aux` and `InterpReduceCollapse.repeat_iter_borrows_merge`. No Lean translation was emitted. This attempt therefore does not resolve the loop-translation issue and establishes no source refinement. It ran under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`; outer wall time was 0.52 s, peak RSS 87,648 KiB, swap 0. The inner Aeneas invocation was likewise 0.43 s / 87,648 KiB / 0 swap. No Rust/Cargo or Charon phase ran. Remote `target/` is excluded.

The saved attempt includes the launch receipt, exact command, time logs, LLBC copy, tool/runner pins and Aeneas failure log. The parent a/b evidence bundle remains unchanged. No serializer translation or Lean compile is claimed.
