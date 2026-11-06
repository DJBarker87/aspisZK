import NKO_FinishDomain
import NKO_C05Core
import NKO_Offsets
import NKO_ViewRanges
set_option autoImplicit false
noncomputable section
namespace NKO_C09
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
def Holds (proof : Slice U8) : Event → Prop
 | .finish v p a _ => NJU_FinishInput.Holds proof v p a
 | _ => True
end NKO_C09
open Lean Elab Tactic
elab "nko_c09_record" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not writer property"
 unless t.getAppArgs.back!.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let t ← getMainTarget
 if t.getAppArgs.back!.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.finish then
  evalTactic (← `(tactic| exact (by
   have post := by
    apply NKO_QueryPost.returned (fields := $(mkIdent `fields)) (start := $(mkIdent `start))
    · assumption
    · apply NKO_Branch.continued <;> assumption
    · apply NKO_Branch.continued <;> assumption
   apply NKO_FinishDomain.writeback (fields := $(mkIdent `fields))
   · exact post.1
   · exact post.2
   · assumption
   · exact NKO_ViewRanges.round0 $(mkIdent `proof) _ (by assumption)
   · exact NKO_ViewRanges.round1 $(mkIdent `proof) _ (by assumption)
   · exact (NKO_ViewRanges.final_message $(mkIdent `proof) _ (by assumption)).1
   · exact (NKO_ViewRanges.final_message $(mkIdent `proof) _ (by assumption)).2)))
 else evalTactic (← `(tactic| exact True.intro))
