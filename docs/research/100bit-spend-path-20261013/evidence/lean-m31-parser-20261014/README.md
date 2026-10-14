# M31 parser refinement evidence

This bundle records focused Lean compilation for the extracted M31 parser and its current-array refinement. It preserves all 11 receipt-backed attempts at the pinned NUC workspace and archives the five selected final `.olean` objects together with the imported codec/Aeneas objects.

The final modules are `R1ExtractedM31Parser` (attempt b), `R1M31ParserRefinement` (attempt d), `R1M31ParserCanonicality` (attempt b), `R1M31ParserArray` (attempt b), and `R1M31ParserCheckpoint` (attempt a). The checkpoint emitted 12 `#print axioms` reports. Its component route imports the extracted parser, the retained word/field codec, the parser refinement, canonicality facts, and the fixed-size array adapter. The reports list only `propext`, `Classical.choice`, and `Quot.sound`, except the reused word roundtrip report, which lists `propext`.

The Lean results establish the statements in those modules about the extracted function, its relationship to the retained M31 byte decoder, and canonical successful values. This bundle does not establish a Rust-source refinement theorem, caller-level parser behavior, or any protocol/security claim. Attempt snapshots, receipts, checksums, output/time logs, imported-source hashes, runner pins, and the checkpoint audit are recorded in `source-manifest.json`; failed attempts and every refinement-c snapshot is retained under its failed receipt-backed attempt.

Source base: `e2f01d0fc9aaf70bbf99c86c7764526233e0be5a`.
