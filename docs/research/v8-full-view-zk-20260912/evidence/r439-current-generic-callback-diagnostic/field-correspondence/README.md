# R439 field declaration comparison

This is a mechanical comparison of selected R439 generated Lean declaration blocks with the raw R156 generated Lean blocks, plus the R161 source-custody notes. It does not establish execution correspondence, semantic equivalence, canonicality assumptions, or proof reuse.

R439 was translated from input LLBC SHA-256 `d28419f408e6bab79c80859db37e137f4ab62b6bd73c7c5a5d909582308a75b9`, with launch revision `54e804310fa3f8dbf4dfc0afe4343ba94247542e` and projection revision `e0d03f10e3834608a06d3b62af3e2f7abfba8c4a`. Its generated Funs, Types, and translation manifest hashes are in `comparison.json`.

The declaration extractor compared full doc-comment/declaration blocks. R439 vs raw R156 blocks match exactly for `QM31.add`, `QM31.mul`, `CM31.add`, `CM31.mul`, `M31.add`, and `M31.mul`. The `M31`, `CM31`, and `QM31` type blocks also match exactly. The mappings are by Rust/Lean declaration names and source paths/lines, not by assuming stable numeric IDs: notably `QM31.add` is ID 321 in R439 and ID 317 in R156; the other listed function IDs and the three type IDs are included in `comparison.json`.

There is one existing representation detail relevant to the promoted cache. R156 raw generated `M31.mul` spells the shift operand `31#i32`; promoted `AspisR156FullFreeze/FunsCore.lean` spells it `31#u32`. R161 `provenance.md` records this as a literal API adaptation, and its `FunsCore-adapter.diff` records the edit. R439 raw output matches R156 raw output, including the `i32` spelling; the promoted block matches R439 after that single literal normalization.

Existing custody/evidence locations:

- `docs/research/v8-full-view-zk-20260912/evidence/r161-current-base-arithmetic/` records the R156 extraction/translation inputs, retained source files, hashes, raw generated Funs/Types, promotion adapter, and R161 focused proof receipts. Its selected `field.rs` source SHA-256 is `639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499`.
- `docs/research/v8-full-view-zk-20260912/evidence/r166-current-circle-execution/manifest.json` records focused R164/R165 receipts and references R161 source pins. `R164ProductExecution.lean` and `R165QuarticExecution.lean` import `AspisR156FullFreeze`; the former proves the selected canonical product boundary, while the latter states encoded `QM31.add` and other quartic operations.
- `docs/research/v8-full-view-zk-20260912/evidence/r174-gamma-batch-step/sources/R174GammaBatchStep.lean` calls `field.QM31.mul` and `field.QM31.add` in `rawCallMut`, and proves the local `rawCallMut_closed` equation over those calls.

This report is based on generated declaration text and retained evidence references only. It does not assert that the two namespaces are interchangeable or that the R439 run proves any field theorem.
