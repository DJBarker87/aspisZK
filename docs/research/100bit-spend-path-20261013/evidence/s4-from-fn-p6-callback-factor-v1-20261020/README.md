# Generated S4 callback factor and closure preservation

This packet proves that the generated `fast_dots.four_dots` `FnMut.call_mut` body factors into its exact generated callback prefix followed by `wideAdd`, and any successful callback result preserves the closure state. The prefix uses the P6 stateful `from_fn` operational model. Universal correspondence to Rust `core::array::from_fn` remains an explicit P6 boundary.

The proof follows the emitted monadic body and preserves operation order. The focused normalization is `Aeneas.Std.uncurry`, identified in the raw Lean Expr dump as the generated pair-callback adapter, followed by `result_bind_assoc` and `bind_tc_ok`. No generated body, resource option, axiom, or external stub was introduced. Both theorems have standard axioms only: `propext`, `Classical.choice`, `Quot.sound`.

V28 was rerun once to repair missing launch-time evidence. Its preflight and command record the source revision and the actual first-selected owners. In particular, the selected P6 operation is the rebuilt object `2d371cd…` in `/tmp/s4-p6-clean-repair-compile`, not the old packet object `e260cb…`; its selected FunsOpsV4 object is `e387b42…`, not the stale `cedc2b…` entry in earlier metadata. The source hashes are unchanged and recorded in the import map. The prior compile revision for the rebuilt P6/FunsOps owners was not captured, so the packet does not infer one.

V20 is excluded because its runner continued after lock acquisition failed and overlapped another Lean process. V21–V27 are retained as failed proof diagnostics. The V25 raw Expr dump identifies `Aeneas.Std.uncurry` as the exact obstruction.

N=8 callback consumption into the fixed-value representation, and the Rust std `from_fn` universal correspondence, remain open. No binary is included.
