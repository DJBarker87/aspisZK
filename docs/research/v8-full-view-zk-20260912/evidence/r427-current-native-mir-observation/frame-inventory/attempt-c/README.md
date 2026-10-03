# R427 attempt-C MIR frame inventory

The complete framed capture is preserved byte-for-byte in `mir-frame.txt` (40,836 bytes, 707 lines, SHA-256 `fd0837471c1031ed080461d83318c058db78fc60ccbcaa60ea8b9e6fe92fb7e9`). `inventory.json` records the complete begin/end frame byte and line bounds, all printed BasicBlockData terminator contexts, every marker verbatim with line and byte offsets, and the audit counts. `inventory_frame.py` deterministically derives that inventory from the preserved frame.

The frame identifies `core::iter::traits::iterator::Iterator::try_fold`; its recorded default display name is `std::iter::Iterator::try_fold`. Its MIR phase is `Runtime(Optimized)`. The printed local declaration for `_1` has `mutability: Not` and type `&'{erased} mut Self/#0`, and the debug variable entry says `self => _1`.

All five blocks with emitted Call-argument markers are listed here; exact entire terminators, argument marker lines/spans, and byte ranges are in `inventory.json`.

| Block | Printed call terminator | Ordered call argument marker(s) |
|---|---|---|
| `bb1` | `_5 = <Self as std::iter::Iterator>::next(copy _1) -> [return: bb2, unwind: bb16]` | arg 0 `copy _1`, iterator.rs `2493:29–2493:33 (#0)` |
| `bb3` | `_9 = <F as std::ops::FnMut<(B, <Self as std::iter::Iterator>::Item)>>::call_mut(move _10, move _11) -> [return: bb4, unwind: bb16]` | arg 0 `move _10`, `2494:21–2494:22 (#0)`; arg 1 `move _11`, `2494:21–2494:32 (#0)` |
| `bb4` | `_8 = <R as std::ops::Try>::branch(move _9) -> [return: bb5, unwind: bb16]` | arg 0 `move _9`, `2494:21–2494:32 (#0)` |
| `bb8` | `_0 = <R as std::ops::FromResidual>::from_residual(move _14) -> [return: bb9, unwind: bb16]` | arg 0 `move _14`, `2494:32–2494:33 (#6956)` |
| `bb10` | `_0 = <R as std::ops::Try>::from_output(move _16) -> [return: bb11, unwind: bb16]` | arg 0 `move _16`, `2496:15–2496:20 (#0)` |

The specific `next` terminator is on `bb1`, with destination `_5`, normal target `bb2`, unwind target `bb16`, and the sole emitted argument record `copy _1`. Its terminator source marker is line 640; the argument marker is line 641. The local declaration and source mapping are retained in the full frame rather than reconstructed from the summary.

There are 40 statement-source markers, 17 terminator-source markers, six call-argument markers across five Call blocks, and 11 `Use` retag markers. The retag markers (all literal `retag=Yes`) are: `bb0` statements 1,2; `bb3` statements 1,8,9; `bb7` statements 0,1,2; `bb8` statement 1; and `bb10` statements 2,3. For each marker, `inventory.json` retains the literal source-info/retag text and exact frame line/byte offsets. Statement/terminator source markers give the complete file/line/column/span and scope records.

This inventory describes the captured Rustc MIR debug output only. It makes no ownership, borrow, Rust-source-to-MIR, callback, or proof claim.
