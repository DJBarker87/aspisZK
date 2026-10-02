# R292 reverse batch-loop inventory

Read-only inventory of only `batch_loop2.body` and `batch_loop3.body` from the saved R292 output. Parent batch, loops 0/1, and outer schedule are excluded. The generated source is `.../r292-private-batch-translation/generated/AspisR292PrivateBatch/Funs.lean`, SHA-256 `4d40a5b7b540adec90efef80a5ed8a5b4403704b388506af21f357761d95aec4`; manifest SHA-256 `4d9a838bceacbd9988607bc15ca196d2f60872ee876e32dc59e7275011379006`.

`batch_loop2.body` maps to frozen `r110_norm.rs:66:38–66:107`; `batch_loop3.body` maps to `r110_norm.rs:67:38–67:107`. The exact generated definition blocks and source lines are in `snippets/`. After renaming only the paired formal variables (`xs/ys`, `px/py`, `ix/iy`, `ix1/iy1`, `ox/oy`, `ox1/oy1`) and the body name, the two Lean blocks are byte-equal. Their separate block hashes and common normalized hash are recorded in `inventory.json`.

The bodies' explicit helper/type references are: `Rev` over `Range Usize`, the `DoubleEndedIterator` dictionary for `StepUsize`, `Rev.next`, `Usize.wrapping_sub`, `Vec.index` and `Vec.index_mut` at `SliceIndexUsizeSlice B`, the `index_mut` writeback closure, `Slice.index_usize`, and the local `B.mul`. They return `Result (ControlFlow ...)` with `done`/`cont`. They also use `Slice B`, `Vec B`, `Std.Usize`, `Rev (Range Usize)`, `ControlFlow`, and tuple products. The generated module imports `Aeneas` and opens `Aeneas.Std`; this inventory does not validate builtin implementation semantics or choose proof premises.

The saved R292 function/type external template holes are enumerated in `inventory.json`. A direct textual scan of these two function blocks finds none of the five function holes or the `Chain` type hole. That is limited to these exact loop-body blocks; the other R292 definitions and transitive implementations may refer to them.

For context only, the repository has a separate R249 definition of the R110 `B.mul` operation over the same `Std.U32` alias; this inventory does not decide reuse or prove a bridge to it. No raw adapter was edited or compiled.
