import R1Z.PV_Src_ResultControl
import R1Z.BuilderRecordsFields

/-! Proof-local Result inversion. It checks the monadic head before applying
inversion, drops the old continuation by FVarId, and uses explicit fresh names.
This automation generates ordinary kernel-checked terms, not source axioms. -/
open Lean Meta Elab Tactic

namespace R1Z.PV_Src_CompilerTactic
private def bindHead (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some n => n.toString.endsWith ".bind" || n.toString.endsWith ".bind_tc"
  | none => false

elab "pv_peel " h:ident " with " v:ident hv:ident : tactic => do
  let old ← withMainContext <| getFVarId h
  let lhs ← withMainContext do
    let ty ← instantiateMVars (← old.getType)
    unless ty.isAppOfArity ``Eq 3 do throwError "expected a Result equation"
    pure ty.getAppArgs[1]!
  unless bindHead lhs do
    let head ← withMainContext <| withTransparency .reducible <| whnf lhs
    unless bindHead head do
      throwError "not a monadic head: {head.getAppFn}"
  let vFresh ← mkFreshUserName `pv_value
  let eqFresh ← mkFreshUserName `pv_equation
  let nextFresh ← mkFreshUserName `pv_next
  let vs := mkIdent vFresh
  let es := mkIdent eqFresh
  let ns := mkIdent nextFresh
  let inv := mkIdent ``R1Z.BuilderRecordsFields.bind_ok_inv
  evalTactic (← `(tactic| obtain ⟨$vs,$es,$ns⟩ := $inv $h))
  let vi ← withMainContext <| getFVarId vs
  let ei ← withMainContext <| getFVarId es
  let ni ← withMainContext <| getFVarId ns
  let goal ← getMainGoal
  let goal ← goal.clear old
  let goal ← goal.rename vi v.getId
  let goal ← goal.rename ei hv.getId
  let goal ← goal.rename ni h.getId
  replaceMainGoal [goal]

end R1Z.PV_Src_CompilerTactic
