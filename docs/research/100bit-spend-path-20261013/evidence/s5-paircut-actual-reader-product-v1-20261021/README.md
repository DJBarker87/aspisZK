# PairCut actual-reader product specialization v1

This target composes the selected-range decoded-product theorem with the transparent-reader adapter. For a successful range run whose read function is `readerBody actualPairDecoder`, it returns the same indexed `CallbackRangeTrace`, accepted EbyK push trace, finish result, and decoded product sum. Canonicality of each successful field read is discharged by `actualReader_eq_checkedCallback` and the retained checked decoder theorem; it is not a separate hypothesis.

The target is an accepted-run theorem, not forward totality. The checked range/product theorem and decoder adapter are imported by exact source/object pin. `review/check_loop_body_order.py` documents the separate generated `push_byte_products_loop.body` inspection: its source operation sequence agrees with the hand-parameterized `pushByteProductsBodyWith` skeleton after substitutions for `IteratorRange.next` and the reader. This is a structural source check only. The generated body has not yet been imported into Lean and no equality theorem connects it to the manual skeleton.

The PairCut extraction is a normalized candidate with other Pair arithmetic/helpers opaque; full unchanged current caller, Rust Std/LLBC runtime refinement, and production adoption remain open. Standard Lean axioms only for the proved theorem: `propext`, `Classical.choice`, `Quot.sound`.
