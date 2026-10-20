# Generated S4 N=8 array field bridge

The checked theorem consumes the generated `FourDotsOps.arrayFromFn 8#usize` field call, instantiated with the exact generated `FnMut` callback ABI. The adapter overrides only length-eight calls with the P6 array operation; other lengths retain the supplied operation. From successful field execution it derives the eight ordered array reads and M31 reducer results through `innerArrayP6_success_values_match_fixedV6`.

This is a field-level caller bridge. The full generated `four_dots` call success and universal Rust `core::array::from_fn` correspondence remain open. The latter remains the explicit P6 library boundary. No Lean binaries are included.
