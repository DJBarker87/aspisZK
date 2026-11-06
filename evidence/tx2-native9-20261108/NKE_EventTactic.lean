import Lean
import NKE_CommonClauses
open Lean Elab Tactic
/-- Only visible writer constructors are eligible. Never unfold an opaque child
while searching for a log combinator. -/
private def nkeRun : TacticM Expr := do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not a writer clause"
 return t.getAppArgs.back!

elab "nke_bind" : tactic => do
 let m ← nkeRun
 unless m.isAppOf ``Bind.bind do throwError "not a visible bind: {m.getAppFn}"
 evalTactic (← `(tactic| apply NKE_EventAll.bind_all))

elab "nke_lift" : tactic => do
 let m ← nkeRun
 unless m.isAppOf ``MonadLiftT.monadLift || m.isAppOf ``liftM do
  throwError "not a visible lift: {m.getAppFn}"
 evalTactic (← `(tactic| exact NKE_EventAll.lift_all _ _))

elab "nke_record" : tactic => do
 let m ← nkeRun
 unless m.isAppOf ``NJU_Log.record do throwError "not a visible record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let t ← getMainTarget
 let e := t.getAppArgs.back!
 if e.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.query then
  evalTactic (← `(tactic| exact NKE_QueryReturn.observed_exact _))
 else if e.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.pending ||
   e.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.flush then
  evalTactic (← `(tactic| rfl))
 else evalTactic (← `(tactic| exact True.intro))
elab "nke_intro" : tactic => do
 let t ← getMainTarget
 unless t.isForall do throwError "not a visible binder"
 evalTactic (← `(tactic| intro value))

elab "nke_pure" : tactic => do
 let m ← nkeRun
 unless m.isAppOf ``Pure.pure do throwError "not a visible pure"
 evalTactic (← `(tactic| exact NKE_EventAll.pure_all _ _))
elab "nke_zeta" : tactic => do
 let m ← nkeRun
 let .letE _ _ value body _ := m | throwError "not a visible let"
 liftMetaTactic fun goal => do
  let target ← goal.getType
  let args := target.getAppArgs
  let next := mkAppN target.getAppFn (args.pop.push (body.instantiate1 value))
  return [← goal.change next]
