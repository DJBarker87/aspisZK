# S4 `from_fn` P6 interface checkpoint

This checkpoint records the green, source-only Lean chain for the operational P6 model at the generated Aeneas callback ABI and its S4 `FourDotsOps.arrayFromFn` adapter. It is a standard-library correspondence model, not a proof that Rust `core::array::from_fn` is universally equivalent to this model. The P6 boundary and finite differential-test support are retained explicitly.

`fnMutStep` calls the exact generated `FnMut.call_mut`, carries the returned callback state, and increments the Usize index. The generic model records the ordered list and final callback/index state. `packArrayState` packages that list as the exact-length Aeneas array, preserving failure and divergence. The S4 adapter overrides only the N=4 field call and leaves other lengths on the supplied `FourDotsOps` operation. The final theorem specializes this adapter to the generated `fast_dots.four_dots` callback and its `(q1,g)` closure input.

The selected generated owner is the current S4 `FunsOpsV4` source/object family (`1786cd…` / `cedc2b…`), not the stale `e387…` owner. The cached Aeneas array object is pinned by object hash; its package source was not retained in this compile kit, so the source-level correspondence of `Aeneas.Std.Array.Array` remains part of the imported Aeneas package boundary.

The earlier attempted theorem for the whole generated `four_dots` body is excluded: its axiom audit included `core.fmt.Formatter`. This packet contains only the three standard-axiom-clean trace theorems in `S4FourDotsP6ArrayOperationV1`.

No binaries are included. `manifest.json` hashes every packet file. Compiler source revision was not captured at launch; the exact source hashes, compiler binary hash, command family, process time/RSS/swap logs, and selected object hashes are retained. The current repository HEAD at packet assembly is not asserted as the historical compile revision.
