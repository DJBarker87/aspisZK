# R486 parser canonical-mask arithmetic

R486 compiled successfully in the pinned Lean 4.32 cached workspace. The promoted Lean source matches the successful run snapshot byte for byte. Compilation source revision: `fb4151c6c0e5d1e582a246c46261484f7552a8c9` (`research/v8-r64-guarded-m31-20260929`). Lean target SHA-256: `5cb94efd84f449a613bbb6de41899ccf7db9683acde009e2b53ce8faa18b7597`.

The associated selected Rust file, copied alongside this evidence, is `r105_parse.rs`, SHA-256 `f6ede1297591906bfe9f975d437402014f63392b1b1a9e081b0f88b59432b91b`. Its fast-path source contains the wrapping-word update `invalid |= x | x.wrapping_add(1)` and rejects when `invalid >> 31 != 0`. The Lean development proves the corresponding 32-bit word/list-fold arithmetic: starting from zero, the acceptance mask has top bit zero exactly when every input word is strictly below `2147483647`. It covers all 32-bit word patterns, including noncanonical patterns, and retains negative examples for `2147483647` (the field modulus), `2147483648` (high bit), and `4294967295` (maximum u32).

## Proof boundary

This proves the word operation and list-fold mask invariant only. It does not prove Rust/Aeneas execution correspondence, byte alignment or `align_to`, `chunks_exact`, vector pushes, fallback parsing, input-length validation, returned parsed values, or complete parser behavior. The first remaining source proposition is a faithful bridge from the actual Rust alignment/chunk/loop/push program and input byte layout to this word/list-fold model, including its success and error outcomes. No privacy or end-to-end security claim follows.

## Compilation record

Exact target: `AspisV8R19/R486ParserCanonicalMask.lean`. Command: `lake env lean -j1 -M4500` in the pinned cached workspace, under `systemd-run --user --wait --collect --pipe` with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Peak RSS is GNU time's Lean-child RSS in KiB.

- Successful run `1791039815045526000`: exit 0; wall 1.55 s; peak RSS 3,723,380 KiB; swap 0.
- Failed run `1791039481524716000`: exit 1; wall 1.57 s; peak RSS 3,709,280 KiB; swap 0. Its attempted native `bv_decide` introduced the extra axiom `step_accepted._native.bv_decide.ax_1_5` and errors; the failed report also contained `sorryAx`.
- Failed run `1791039746354800000`: exit 1; wall 1.48 s; peak RSS 3,709,080 KiB; swap 0. It recorded symbolic rewrite errors and `sorryAx`.

## Complete successful `#print axioms` output

```text
'AspisV8R19.R486ParserCanonicalMask.step' depends on axioms: [propext, Quot.sound]
'AspisV8R19.R486ParserCanonicalMask.accepted_iff' depends on axioms: [propext]
'AspisV8R19.R486ParserCanonicalMask.step_accepted' depends on axioms: [propext, Quot.sound]
'AspisV8R19.R486ParserCanonicalMask.accumulated_accepted' depends on axioms: [propext, Quot.sound]
'AspisV8R19.R486ParserCanonicalMask.complete_mask' depends on axioms: [propext, Quot.sound]
'AspisV8R19.R486ParserCanonicalMask.rejects_prime' does not depend on any axioms
'AspisV8R19.R486ParserCanonicalMask.rejects_high_bit' does not depend on any axioms
'AspisV8R19.R486ParserCanonicalMask.rejects_max' does not depend on any axioms
```

The evidence directory preserves the exact snapshots, receipts, complete logs, and associated Rust source. `SHA256SUMS.txt` checksums these files and this report.
