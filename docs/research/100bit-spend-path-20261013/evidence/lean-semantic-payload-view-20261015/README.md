# Semantic payload view — focused Lean evidence

`R1SemanticPayloadView` maps typed row payloads into the older 25-row semantic message parser view. The C2 root is represented through an explicit `recoverC2` callback. This module proves parser-shape and row-selection facts only; it does not assert a Rust source correspondence, an extraction theorem, or protocol acceptance.

The focused NUC target `R1SemanticPayloadView` passed on attempt `semantic-payload-view-w` (exit 0, 4.39 s, 3,573,472 KiB peak RSS, zero swap; `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`). All eight public `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The bundle retains all 23 exact attempts: a–v failed proof drafts and w green. Every attempt source snapshot matches its receipt and both source hash sidecars. The final object is stored only in the deterministic archive; there are no loose `.olean` files. See `source-manifest.json` for source/object pins and complete file hashes.

## J1.R4 source-pin repair

The two direct imports now include source snapshots and SHA-256 pins:
`R1SemanticRecordCodec` and `R0P.MaskView`. The snapshots were copied from
`lean-semantic-payload-opening-view-20261015/sources` at revision
`136b746805f3438507732622c9b4e50f36bf49f9` and also match the repository files
at the original `57edab99fe104f23b3d3c881d1e87c1abb0975c0` source revision.

This is a retrospective packaging repair, without a Lean replay. Original
compile receipts, object pins, source revision and resource measurements are
unchanged. It does not establish an unrecorded compile-time source-to-object
attestation. Historical audits that name the previous manifest hash remain
valid observations of that previous manifest; `source_pin_repair` records its
hash and exact Git object. This repair does not close byte/source refinement.
