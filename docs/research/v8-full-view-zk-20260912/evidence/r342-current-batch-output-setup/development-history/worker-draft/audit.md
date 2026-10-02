# R342 exact output-fragment composition draft audit

Uncompiled scratch-only proof draft. It imports the staged R340 raw output fragment and promoted R311 reverse-loop model.

The model-only `zeroVec xs` uses `List.replicate xs.val.length B.ZERO` and the existing `Slice` size bound. `from_elem_zeroVec` applies the pinned `alloc.vec.from_elem_spec` with the copied R340 Clone implementation; the clone result is `rfl`, and the postcondition identifies the actual returned vector with `zeroVec xs`. `output_reverse_range_default` records the exact default reverse adapter result from the existing Aeneas Std definition.

`reverseModel_output_length` is a structural induction using only R311's `setNat_length`. `selectedOutput0_model` requires only nonempty source length, canonical source values at indices `1 ≤ j < xs.length`, and prefix values for `j < xs.length - 1`; the reverse-loop source read, prefix read, iterator end, initial output capacity, final index-zero bound, and output-vector equality are derived in the proof. Its result is the actual R340 `selectedOutput0` returning the reverse model's output after writing its accumulated value to index zero. `selectedOutput1_eq_selectedOutput0` is definitional (`rfl`), and `selectedOutput1_model` reuses the first result.

No caller prefix-success result, full batch guard, nonzero condition, explicit extra capacity, independent Rust Std semantics, or compiler correspondence is added or claimed. The allocation, reverse adapter, reverse loops, and mutable vector indexing use the pinned Aeneas Std/previously established execution API. `#print axioms` commands are included for helper and public theorems; no Lean compile was run.
