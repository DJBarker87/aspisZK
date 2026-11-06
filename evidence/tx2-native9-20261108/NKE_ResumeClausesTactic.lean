import NKE_ResumeClausesCore
open Lean Elab Tactic
/-- Do not try a tail theorem at an unrelated head: that would unfold the
whole remaining source while performing unification. -/
elab "nke_resume_tail" : tactic => do
 let t := (← getMainTarget).consumeMData
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not writer property"
 let m := t.getAppArgs.back!.consumeMData
 let h := m.getAppFn.constName?.getD Name.anonymous
 unless ["NJU_ResumeObserved.finishTailG","NJU_ResumeObserved.queryEndG",
  "NJU_ResumeObserved.queryMidG","NJU_ResumeObserved.queryBlockG",
  "NJU_ResumeObserved.resumeBodyG"].contains h.toString do throwError "not a literal tail"
 let n := (h.toString.replace "NJU_ResumeObserved." "NKE_ResumeClauses.").toName
 evalTactic (← `(tactic| apply $(mkIdent n)))
