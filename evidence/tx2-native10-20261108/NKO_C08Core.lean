import NKO_QueryPost
import NKO_C05Core
set_option autoImplicit false
noncomputable section
namespace NKO_C08
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
def Holds : Event → Prop
 | .flush pending weights reply => pending.raw.val.length=64 ∧ weights.val.length=64 ∧
   reply=ok (NJJ_Flush.output pending)
 | _ => True
end NKO_C08
open Lean Elab Tactic
elab "nko_c08_record" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not writer property"
 unless t.getAppArgs.back!.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let t ← getMainTarget
 if t.getAppArgs.back!.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.flush then
  evalTactic (← `(tactic| exact (by
   have sizes := by
    apply NKO_QueryPost.widths (fields := $(mkIdent `fields)) (start := $(mkIdent `start))
    · assumption
    · apply NKO_Branch.continued <;> assumption
    · apply NKO_Branch.continued <;> assumption
   exact ⟨sizes.1,sizes.2,NJJ_Flush.source _ _ sizes.1 sizes.2⟩)))
 else evalTactic (← `(tactic| exact True.intro))
