# R297 monomorphized private norm batch extraction

R297 repeats the accepted metadata-valid R294 batch extraction with the same frozen source root, starting function, includes, Rust flags, Cargo features, optimized cached release settings, and toolchain. Its only Charon-option change is adding the boolean `--monomorphize` before `--dest-file`; the R294 source remains unchanged. This focused option change tests whether specialization yields signatures acceptable to the pinned Aeneas translator. No declaration or signature edits are made.

The extraction is in a fresh remote root and isolated systemd scope (MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128). The runner records exact command, local launch revision, verified frozen source hashes, monomorphize flag, source/body census, metadata `has_errors`, wall/RSS/swap, and full logs. R294 and R295 artifacts remain unchanged. This extraction is diagnostic only; no translation or proof claim is authorized before lead review.

## Observed extraction result

The optimized Charon command exited 0 and wrote `R297PrivateNormBatch.llbc` (SHA-256 `6c2caba33f39adecdfc7c4facd7444ab66d505956d51036d52765b1340f84de0`) with `has_errors=false`. Root Fun0 is local and has a body; its type-parameter list is empty. It remains in original Charon ordering at group index 76. Declaration counts are 29 types, 52 functions, 3 globals, 12 traits, and 26 trait implementations.

The saved postflight census records the root body’s 63 call nodes: 59 regular function targets (21 distinct IDs) and 4 builtin index calls. Its transitive regular-call graph contains 38 functions. Relevant reachable declarations are:

- Fun24, the instantiated `Chain` Iterator `try_fold` implementation, has a transparent body and no residual generic type parameters or binder type constraints.
- Fun36 and Fun38 are instantiated `Iterator::try_fold` declarations with no residual generic type parameters or binder type constraints, but both remain Foreign/Opaque.
- The same reachable chain-fold body references instantiated `ControlFlow::branch`, `from_output`, and `from_residual` declarations (Fun37, Fun39, Fun40), which remain Foreign/Opaque.

The complete rooted call census, exact function IDs and source origins are in `postflight-audit.json`. This is LLBC extraction evidence only. R295’s internal Aeneas signature failure remains preserved and unchanged. No translation, template fill, Lean compilation, or proof claim was made.

GNU time reports Charon exit 0, wall 13.60 s, peak RSS 624532 KiB, swaps 0. The systemd unit completed successfully in 13.964 s under the configured 5 GiB high / 7 GiB max / zero-swap / 128-task scope. Exact command, source hashes, host reservations, and full logs are retained.
