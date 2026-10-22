# V10 literal helper source-cut transport

This packet records a kernel-checked all-Result equality between the literal copied V10 `fast_dots.four_dots_one` helper body and the fixed-v6 helper after the `wideFromEbyK` carrier map. The body preserves the emitted effect order; its external operations are represented by the named `ops` slots and adapter definitions in the Lean source. `literal_helper_eq_fixed` is the API for the full-helper transport.

`check_packet.py` token-compares the retained generated V10 body with the `literalV10Helper` cut after exactly seven emitted operation substitutions plus the `four_dots_one_loop0` and `EbyKDot.new` named slots. The generated source SHA is pinned in the receipt. This is source-cut validation; the Lean theorem proves equality of the copied typed body and fixed-v6 model, not Rust `core::array::from_fn` lowering or whole frozen-source adoption. Production sources remain unchanged.

Validation: Lean 4.32.0, `-j1 -M4400`, exit 0, 8.74 s, peak process RSS 3,756,589,056 bytes, compiler swap 0. All three exported theorems have standard axioms `[propext, Classical.choice, Quot.sound]`. The `.olean` is deliberately not packaged.
