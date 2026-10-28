import R1Z.PV_Src_CompilerTactic
open Lean Meta Elab Tactic
namespace R1Z.PV_RunJoin_HeadControl29

/-- Reduce only the equation's head. Deep decoder continuations are shared
unchanged rather than traversed by a recursive simplifier. -/
elab "pv_head " h:ident : tactic => do
  let (old,ty) ← withMainContext do
    let old ← getFVarId h
    let ty ← instantiateMVars (← old.getType)
    unless ty.isAppOfArity ``Eq 3 do throwError "expected equation"
    let args := ty.getAppArgs
    let lhs ← withTransparency .reducible <| whnf args[1]!
    pure (old,← mkEq lhs args[2]!)
  let goal ← getMainGoal
  let goal ← goal.changeLocalDecl old ty
  replaceMainGoal [goal]

/-- Split exactly the head conditional of a Result equation. A rewrite
replaces that one node; it does not simplify the full nested decoder. -/
elab "pv_if " h:ident : tactic => do
  let cond ← withMainContext do
    let old ← getFVarId h
    let ty ← instantiateMVars (← old.getType)
    let lhs := ty.getAppArgs[1]!
    unless lhs.isAppOfArity ``ite 5 do throwError "expected head if"
    Term.exprToSyntax lhs.getAppArgs[1]!
  let fresh ← mkFreshUserName `pv_condition
  let hc := mkIdent fresh
  evalTactic (← `(tactic| by_cases $hc : $cond))
  allGoals fun goal => do
    replaceMainGoal [goal]
    evalTactic (← `(tactic| first | rw [if_pos $hc] at $h | rw [if_neg $hc] at $h))
    getMainGoal

open Aeneas Aeneas.Std Result

theorem smoke (p : Prop) [Decidable p] (h : (let x := p; if x then ok true else ok false) = ok true) : p := by
  pv_head h
  pv_if h
  · assumption
  · cases h
#print axioms smoke
end R1Z.PV_RunJoin_HeadControl29
