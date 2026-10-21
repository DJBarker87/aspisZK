# S4 concrete constructor to prepared-loop producer

This source-only packet replaces the generic constructor parameters in the retained caller-to-prepared-loop producer with the V4 concrete constructor builder. The caller installs `withConcreteConstructorChildren ops filled`, sets the frozen split to 10, and adapts the same query call. From one successful caller run it derives `k = 10`, retains the same prepare result and scanner success, and reaches the corresponding Stage2 query loop with the accumulator cursor zero. The wrapper then applies the explicit same-run `hscanBinding` and `hprepareBinding` to that prepare witness.

The public theorem names and namespace are unchanged from the retained producer: `source_caller_reaches_ten_loop` and `source_caller_reaches_prepared_loop` in `AspisR1S4Tx1TenFieldResultsRootV1`. This packet does not prove the upstream scanner/prepare bindings, allocator behavior (`filled` remains universal), or the full runtime/Rust Std dispatcher boundary.

Both focused Lean targets exited 0 with only standard axioms. Exact source/object pins, Lean binary, pinned path profile, wall time, peak RSS, and compiler swap values are in `proof/receipt.json`. No compiled objects or LLBC artifacts are included.
