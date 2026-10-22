# S9 focused concrete FieldOps instance

This source-only packet composes retained S9 field owners into one explicit `FieldOps` record. `qmMul` remains the accepted current QM multiply; `qmSquare` dispatches to the selected generated square through a fieldwise carrier map; wide add and wide M31 multiply use the current field owner; wide-by-QM31 uses the generated current operation; full wide multiplication uses the current exact multiplication and carrier map; and `iterFold` uses the accepted extracted P6 fold.

The focused theorem set includes exact dispatch equations, `kpowers_concrete_eq_current`, the extracted-fold P6 law, and canonical-input total exact semantics for `wideMul`. It does not claim unconditional success or semantic totality for `wideMulM31`/`wideMulQM31`; their existing result laws remain success-conditional. It also does not yet prove a canonical/decode success law for the installed `qmSquare`. Those are the next source-semantic obligations.

Lean 4.32 focused compile: exit 0, 10.723 seconds, maximum RSS 3,223,060,480 bytes, swap 0. Axiom audits report only `[propext, Classical.choice, Quot.sound]`. The first two projection-notation attempts failed and are retained in `evidence/attempt-diagnostics.md`; neither produced an accepted object.

The selected import closure is pinned in `evidence/import-closure.json` (5,125 modules, zero missing) and its exact search path is in `evidence/LEAN_PATH.txt`. The compiled `.olean` is external; only its path/hash are recorded.
