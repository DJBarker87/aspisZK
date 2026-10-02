# R318 forward-prefix raw staging

This draft stages exactly four generated R292 blocks: `batch_loop0.body`, `batch_loop0`, `batch_loop1.body`, and `batch_loop1`. Each complete doc/attribute/definition block is copied verbatim from the generated Funs file and checked against the four R315 inventory block hashes. There are no source-body edits or local helper shadows.

The target imports Aeneas.Std, R249, and R316. The generated `B` type resolves through the existing R249 alias to `Std.U32`; `B.mul` resolves through the open R249 namespace. Its inherited `Std.U64.wrapping_shr x 31#i32` to `...31#u32` adapter is recorded in the R249 binding audit. `core.slice.Slice.last` resolves through the opened R316 namespace to its actual emitted declaration; R316's sole checked adaptation is `Usize.sub` to `UScalar.sub`. This is binding provenance only; no helper theorem is asserted here.

Other Aeneas.Std dependencies (`IteratorSliceIter.next`, `Vec.deref`, `Option.unwrap`, `Vec.push`, `loop`, and the referenced container/result types) remain explicit library-boundary dependencies. The file adds `#print axioms` for each of the four staged definitions. It has not been compiled, and no loop invariant or source-semantics claim is made.

Run `python3 build_raw.py` to regenerate the staging file and binding audit; both selected-block hashes and R315 inventory are checked before writing. `SHA256SUMS` covers the complete local artifact set.

Root publication review: `pre-wrapper/` preserves original staging builder, source, audit and checksums. The final wrapper adds one `noncomputable section` line; declaration bodies remain exact. The current target hash and successful compilation receipt are in `binding-audit.json` and the parent manifest. The final builder header reflects that wrapper. Its original scratch-relative input paths describe the archived generation workspace.
