# Semantic payload view — focused Lean evidence

`R1SemanticPayloadView` maps typed row payloads into the older 25-row semantic message parser view. The C2 root is represented through an explicit `recoverC2` callback. This module proves parser-shape and row-selection facts only; it does not assert a Rust source correspondence, an extraction theorem, or protocol acceptance.

The focused NUC target `R1SemanticPayloadView` passed on attempt `semantic-payload-view-w` (exit 0, 4.39 s, 3,573,472 KiB peak RSS, zero swap; `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`). All eight public `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The bundle retains all 23 exact attempts: a–v failed proof drafts and w green. Every attempt source snapshot matches its receipt and both source hash sidecars. The final object is stored only in the deterministic archive; there are no loose `.olean` files. See `source-manifest.json` for source/object pins and complete file hashes.
