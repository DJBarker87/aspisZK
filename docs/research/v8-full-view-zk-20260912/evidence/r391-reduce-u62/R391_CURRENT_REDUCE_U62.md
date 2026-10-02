# R391 reduce-u62 focused result

R391 now has a green focused proof module, still in scratch and not promoted. The generated R388 `reduce_u64` body is definitionally equal to the retained R156 reducer after unfolding both implementations and their `P` constants. The extracted release `M31.reduce_u62` wrapper is shown equal to the retained `M31.reduce_u64`; using R161, the wrapper succeeds canonically for every `U64` input and returns the exact `ComplexBaseExecution.encodeBase` value.

The module compiled in run `1790957475592362000`: exit 0, 1.50 seconds, GNU-time child RSS 3,702,548 KiB, swap 0, with Lean `-j1 -M4500` in systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. It prints axioms for the two extracted declarations and four theorems; each report contains only `propext`, `Classical.choice`, and `Quot.sound`. One unused `bind_tc_ok` simp argument warning remains in the successful source; it was left unchanged after review.

R388 generated Types/Funs are preserved byte-for-byte in `generated-source/`. Compile copies differ only in the approved umbrella-import replacement documented in `import-adaptation.diff`; the successful proof also has a matching source snapshot in its run receipt. R387 extraction and R388 order/translation provenance are included under `provenance/`. `verify_bundle.py` passes its offline integrity checks. Full run logs, receipts, source snapshots, failed attempts, cache adaptation, dependencies, and checksums are retained beside this note.

This establishes only the extracted release reducer wrapper result. Caller accumulator bounds, loops, interpolation, and matrix/source-to-model correspondence remain open; this note makes no such claim.

The separate read-only NUC source/cache audit is in `source-cache-audit.json`. It pins R161 and R156 source hashes to the copied files and records the actual R126 `.olean` object paths and hashes. The successful run receipt is unchanged; its direct-local-import map did not include R161, so this supplemental audit records that omission rather than rewriting the receipt. `Aeneas.Std.olean` is also identified by hash.
