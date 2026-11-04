import Lean
/-! Direct proof construction for aliases of identical frozen literal tables.
The kernel checks the resulting Eq.refl against the ORIGINAL equality target.
No oracle, new axiom, conversion admission or recursion-limit change is used.
This avoids recursive simplifier traversal of a 512-cell literal expression. -/
open Lean Meta Elab Tactic in
elab "NEW_literal_refl" : tactic => do
 let goal ← getMainGoal
 let target ← goal.getType
 let some (_,lhs,_) := target.eq? | throwError "expected an equality"
 goal.assign (← mkEqRefl lhs)
 replaceMainGoal []
