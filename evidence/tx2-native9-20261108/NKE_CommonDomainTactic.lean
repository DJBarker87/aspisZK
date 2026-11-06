import NKE_CommonDomainCore
import NKE_EventTactic
open Lean Elab Tactic
elab "nke_domain_record" : tactic => do
 let target ← getMainTarget
 unless target.isAppOf ``NKE_EventAll.Holds do throwError "not a writer clause"
 let run := target.getAppArgs.back!
 unless run.isAppOf ``NJU_Log.record do throwError "not a visible record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let goal ← getMainTarget
 let event := goal.getAppArgs.back!
 let siteName := event.getAppFn.constName?.getD Name.anonymous
 if siteName == `NJU_CommonObserved.Event.geometry then
  evalTactic (← `(tactic| exact ⟨$(mkIdent `start),rfl⟩))
 else if siteName == `NJU_CommonObserved.Event.pending then
  evalTactic (← `(tactic| exact ⟨$(mkIdent `width),rfl⟩))
 else evalTactic (← `(tactic| exact True.intro))

