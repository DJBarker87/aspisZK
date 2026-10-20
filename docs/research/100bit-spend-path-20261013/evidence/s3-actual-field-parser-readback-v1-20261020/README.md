# S3 actual field parser readback

This packet records the checked Lean theorem `AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decodeField_success_parser_readback`. From a successful generated `decodeField bytes i` callback, it recovers a successful call to the actual extracted `weights.field` parser for the same byte slice/index, the exact checked slice boundaries, the decoded `WideExact`, and the corresponding converted callback value.

The proof was checked on the pinned Lean 4.32 NUC closure recorded in `attempts/accepted-v1/`. Receipt: exit 0, 2.307 s, peak process RSS 3,913,280 KiB, cgroup peak 380,166,144 bytes, swap 0. Axioms are `propext`, `Classical.choice`, and `Quot.sound`. The theorem is a success inversion only; it does not establish totality of the parser or the enclosing loop.

`source-provenance/weights-field-selector/` preserves the source selector extraction and mechanical adapter check. The frozen production source `sources/rust/weights.rs` matches the pinned source revision and selector body. Producer receipts for the imported Lean owners are included under `dependency-producers/`. This packet contains source and receipts only, no compiled objects.
