# Actual continuation success to composition canonicality

The theorem `actual_continue_success_composition_canonical` unfolds the unchanged generated `composition_parts_continue` body. It consumes the exact successful results of its four `array_from_fn_copy` calls, selector construction, both evaluator callbacks, selected-column and selected-claim lookups, copy evaluator, multiplier constructor, and both folds. Given canonical `theta`, copy residual, and pointwise canonical callback arrays, it proves the returned composition value is canonical. These are callback-local success/value premises; the theorem asserts neither callback totality nor unproven callback canonicality.

This closes the actual continuation-level result, not yet the enclosing `composition_parts_with_callers` branch that reaches it through amount validation and `validate_transition`. Pointwise canonicality of the 24 semantic and 4 Poseidon callback entries remains the principal arithmetic caller obligation.

Verification: Lean 4.32.0; exit 0; 20.21 seconds; peak aggregate Lean RSS 2,350,563,328 bytes; process swaps 0. Printed axioms: `propext`, `Classical.choice`, `Quot.sound`. Exact source, object, invocation, receipt, log, and direct import pins are included. Base dependency packet: `current-terminal-array-loop-20261019` (published).
