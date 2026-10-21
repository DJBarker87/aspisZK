# S4 concrete accumulator constructor children

This focused Lean result installs the current frozen `Accumulator::new` constructor body with its `final_len`, zero, and one children represented by explicit cases-based carrier maps into the current caller carrier. The only universally quantified operation left is `filled`. From the same successful transaction/query witness, the theorem derives that the initial accumulator cursor is zero.

The target is `AspisR1S4AccumulatorNewConcreteChildrenV4.tx1_success_same_query_initial_next_zero`. Its compiler audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The exact compiler, profile pin, source/object hashes, exit status, wall time, peak RSS, and swap are in `proof/receipt.json`; raw output is retained under `proof/`.

`proof/check_concrete_children.py` checks the pinned Rust and generated source declarations plus the allowed carrier cut. It does not establish Charon/Aeneas semantic correctness. The universally quantified `filled` operation means this packet does not prove allocator behavior. It also does not prove runtime/source dispatcher binding or close the whole S4 transaction cone.

No compiled objects or LLBC binaries are included. Existing accepted source-owner packets are referenced by exact source/object pins in the receipt. The historical accepted generated Funs object was not available in the selected local cache under its accepted manifest hash; this focused proof compiles the source-shaped cut and pins that Funs source, while the theorem does not import that old Funs object.
