# S4 P6 four-step callback trace addendum

This immutable addendum extends the already-published P6 from_fn model packet without modifying it. It records that a successful N=4 operation using the P6 adapter contains four ordered successful calls to the exact generated S4 `FnMut` callback, with the same captured `(q1, g)` closure. It does not yet prove that each output equals the fixed-v6 `four_dots_one` helper, nor that Rust `array::from_fn` is universally equivalent to the P6 model.

`S4FromFnP6FourTraceV1.lean` is standard-axioms clean (`propext`, `Classical.choice`, `Quot.sound`). It imports the exact operation adapter from the referenced immutable packet and proves `fourDotsOuterGeneratedCallback_success_four_steps` by inverting the stateful trace. The callback’s call_mut output state is not yet shown equal to its input closure; the emitted generated body visibly ends with `ok (we2, c)`, and proving this with successful-operation inversion is the next bridge.

The selected `Aeneas.Std.Array.Array` object is pinned to the exact source and producer receipt copied here. The producer pin comes from the retained R18 backend object manifest; three NUC source copies were checked to have the same source SHA. This is Lean package provenance, separate from the P6 Rust-standard-library correspondence boundary.
