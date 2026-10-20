# Query-values prefix forwarding bridge (candidate)

This packet freezes a small source cut at the start of `candidate::query_values`. The four Rust statements at byte range `[6650, 6786)` of the adopted c8 candidate source hash `a6508483fe1144ba83f1ca11b712e39e1dd5c2b96da7330ad442372273eaf6d7` read the current index and query, call `opening(proof, i)`, and call `four_dots(q, g)`. The candidate helper repeats that prefix and returns its locals. The source checker verifies those bytes, the candidate helper's ordered prefix, and the complete emitted Lean function body.

The extracted helper's `opening` and `four_dots` external declarations are not imported into the proof. `ForwardOps.lean` replaces exactly those two call names with explicit typed function parameters, leaving the emitted body, operands, order, and return unchanged. The success theorem proves that a successful result contains the same `q` passed to `fourDotsOp`, and that the call receives exactly the input `g`. Both operations remain explicit caller boundaries; no facts about their implementations are assumed.

The raw generated `Funs.lean` and `FunsExternal_Template.lean` are retained only as extraction evidence. They contain Aeneas resource-option lines and external axiom templates, and are not in the checked Lean import closure. The checked `Types.lean` removes only the two generated resource overrides; `check_source_bridge.py` verifies that mechanical difference. The success theorem's axioms are `propext`, `Classical.choice`, and `Quot.sound`.

This is a candidate source cut. It does not prove the full `query_values` body, caller reachability, the semantic implementations of `opening` or `four_dots`, later folds/checks, or production adoption.
