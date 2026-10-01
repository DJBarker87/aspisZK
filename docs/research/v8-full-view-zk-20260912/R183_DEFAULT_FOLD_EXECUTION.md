# R182/R183 generic default fold execution

The raw generic `Iterator::fold` declarations extracted from the pinned Rust standard library are staged byte for byte in `AspisR182IteratorDefault/FunsDefaultFold.lean`. R183 proves that this default body over the existing Aeneas slice iterator model equals a list fold on the remaining suffix. It visits each element in order, carries the mutable `FnMut` environment, and preserves arbitrary callback errors and divergence. The final fold result discards the environment as the generic source body does. There are no extra correctness premises on the callback.

Both focused targets compiled in the pinned capped Lean 4.32 workspace. R182: exit 0, 0.99 seconds, peak RSS 2,527,876 KiB. R183: exit 0, 1.43 seconds, peak RSS 2,538,208 KiB. Both used zero swaps. All six complete axiom reports are empty or contain only `propext`, `Classical.choice`, and `Quot.sound`. See the [evidence manifest](evidence/r183-default-fold-execution/manifest.json). The failed drafts, source copies, full logs, extraction commands, raw LLBC and Rust standard library source are retained.

This does not establish the pointer-based selected slice fold override. Nor does it resolve the full callback extraction’s captured-borrow `FnMut` interface or vector extension. The raw generic default body is compiled; the remaining full generated files are diagnostic copies and are not imported. No external execution axiom is used.

Next: prove the selected slice override and captured-borrow execution, then vector extension and the complete callback chronology through rho with every failure and oracle call. Privacy and soundness remain open. Verifier source, parameters and CU results are unchanged; no CU benchmark or unchanged regression suite was rerun.
