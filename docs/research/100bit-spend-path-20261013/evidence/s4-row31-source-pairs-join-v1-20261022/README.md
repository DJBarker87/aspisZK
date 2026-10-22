# Conditional row-31 literal/source-pairs join

`AspisR1.S4LiteralRow31PairsJoinV1.row31_success_list_eq_source_pairs` joins the successful literal row-31 payload sampler to the selected eight-pair scanner. It preserves the exact returned `xs`, its `LiteralQueryRead.decode` as `some q`, and proves that the first component of the selected `R4Transport2ScanComposition.pairsRun` is `.ok xs`.

The theorem is conditional on the supplied source/model boundary: it requires the pre-row31 sampler state equality `hstate`, the actual row-31 transcript absorb success, eight ordered source digest successes for the two query labels, and the `hdigest` interpretation for those successful calls. It does not prove generic digest chunking invariance or derive the pre-row31 state equality. The challenge is a `List Nat`, not U32LE bytes. The theorem is a source/model join, not a complete current-caller or production standard-library refinement.

The focused Lean 4.32 run used the exact profile and command in `receipt/`. It exited 0 in 5.712 seconds, peak process RSS 3,426,369,536 bytes, zero swaps. The axiom audit reports only `[propext, Classical.choice, Quot.sound]`. The compiled object is retained outside this source-only packet at `/tmp/s4-literal-row31-pairs-join-v1/objects/` and is not committed.
