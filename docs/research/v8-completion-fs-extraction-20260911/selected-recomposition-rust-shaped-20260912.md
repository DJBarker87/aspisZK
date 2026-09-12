# Selected recomposition Rust-shaped bridge

`lean/SelectedRecompositionRustShaped.lean` independently defines the
field-level shape of the selected Rust recomposition calculation and proves it
equals the already constructed recomposition source value.

The checked bridge covers:

- a 16-opening array with literal reads at indices 0 through 10;
- the reverse iteration over indices 8 through 0, seeded by index 9;
- current, successor, XOR-12 view order;
- the `mul_m31` scalars 1024 and 1,048,576, proved equal to the extension-field
  factors `2^10` and `2^20`;
- the literal selector rows 1008, 1010 and 1012; and
- the final producer-minus-reconstruction sign.

The endpoint is
`rustRecomposition_eq_sourceValue`.  It has no callback-acceptance or terminal
premise.  This is an independently defined mathematical execution of the
pinned loop shape, not an Aeneas translation or a proof of Rust machine
semantics.  Literal Rust-to-functional refinement therefore remains open.

The focused Lean 4.32.0 NUC replay exited 0 in 3.44 seconds with peak RSS
6,610,272 KiB and zero swaps.  All printed declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.  Exact hashes and the compile log are in
`results/v8-completion-fs-extraction-20260911/recomposition-rust-shaped-v1/`.
