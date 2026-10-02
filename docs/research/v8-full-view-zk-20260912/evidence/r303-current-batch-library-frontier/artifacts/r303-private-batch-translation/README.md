# R303 focused Aeneas translation of the R297 monomorphized batch

R303 consumes the exact R297 LLBC with original serialized declaration order and the original pinned Aeneas binary. It makes no input edits or metadata reorderings. Output namespace: `AspisR303PrivateBatch`.

Input gate: SHA-256 `6c2caba33f39adecdfc7c4facd7444ab66d505956d51036d52765b1340f84de0`, `has_errors=false`, root Fun0 local and body-present. Original `ordered_decls` is preserved. Aeneas binary SHA-256 `63b04a88532b8fb0aaa0d274881b5cacf00bc4f449243ece905178f0de9cc495`. Launch preparation revision: `b87e6b73671c5bf747de1b0bf3dd324fc428912c`.

The capped command uses sequential translation, abort-on-error, Lean backend, split files, and JSON manifest in its own 5 GiB high / 7 GiB max / zero-swap / 128-task systemd scope. Saved outputs include full logs, resource reservation, root emission check using the opened-namespace `def` name, generated file hashes, warnings, and external template axiom names. Any opaque/axiom template declarations remain unfilled. This is a translation artifact inventory only: no Lean compile, template fill, axiom audit, proof result, or source-correspondence claim.

## Observed translation result

Aeneas imported the exact pinned R297 LLBC and exited 2 before emitting a generated directory or manifest. It reported `Unexpected erased region` at `iterator.rs:2486:4–2490:35`, in `SymbolicToPureTypes.ml:848`, while computing back-type levels for an instantiated signature. The full stack and GNU time report are preserved in `translate.log`; `translation-result.json` records no generated root or template holes. This is a different translator failure location from R295's empty-`trait_type_constraints` assertion, and no retry or translator change was made.

No R303-generated helpers exist to inventory because translation aborted before output. The input LLBC's prior R297 census still identifies reachable Foreign/Opaque declarations: instantiated `Iterator::try_fold` Fun36 and Fun38, `ControlFlow::branch` Fun37, `ControlFlow::from_output` Fun39, and `ControlFlow::from_residual` Fun40. These are input metadata only, not accepted assumptions or filled template axioms.

GNU time reports exit 2, wall 0.20 s, peak RSS 69,168 KiB, swaps 0. The isolated systemd service reports runtime 339 ms and zero swap. No Lean compile, template fill, axiom compile, or proof claim was made.
