# R426 saved extraction provenance inventory

This is a read-only inventory of the saved R396/R327 Rust-to-LLBC extraction evidence and the later R385/R389 translator-candidate evidence. No compiler, extraction, translation, or proof job was run for this inventory.

The pinned selected Rust source contains the generic `Iterator::try_fold` body at `iterator.rs:2486–2497`; its loop calls `self.next()` at line 2493. R396's decoded LLBC identifies `Iterator::try_fold` as function 58 with source span `iterator.rs:2486:4–2490:35`. In that saved LLBC the `Iterator::next` call is statement 4440 inside loop statement 4600, and its receiver operand is `Copy Local(1)` typed as `&'Body1 mut Self`. This inventory records that syntax/type as emitted. It does not infer the earlier rustc MIR ancestry.

The recorded extraction command requests Charon `--mir built`. R396 leaves `--monomorphize` unset; R327 includes `--monomorphize` and produces a different LLBC artifact. R385 is a translator-source candidate/build, and R389 runs translation on unchanged R327 LLBC. The saved command/provenance set contains no request for rustc `-Zdump-mir`, `--emit=mir`, or a THIR dump. A recursive search of the current repository checkout found no `.mir`, `.thir`, or `.thir-tree` files. This is a checkout-scoped negative inventory, not proof that no such artifact exists elsewhere on the build host.

The selected LLBC body has no explicit `Retag` or `CopyForDeref` operation after Charon lowering. The current saved artifacts therefore do not tell whether the `Copy &mut Self` operand originated from a frontend temporary reborrow or which Retag events preceded it. Further original MIR/THIR provenance would be needed to answer that.

`inventory.json` records source paths, hashes, command-mode facts, statement IDs, and search scope. `R396-selected-try-fold-callees.json` is copied byte-for-byte from the saved focused audit. The two Rust excerpts are byte-derived line-numbered views from the pinned source files listed in the JSON. This is provenance only; it makes no source-semantics or proof claim.
