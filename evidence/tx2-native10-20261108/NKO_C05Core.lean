import NKO_C03Core
import NKO_Branch
import NKE_GeometryDomain
import NKE_ResumeWidth
set_option autoImplicit false
noncomputable section
namespace NKO_C05
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
def Holds : Event → Prop
 | .query _ _ _ _ geometry _ _ =>
   geometry.start=10#usize ∧ geometry.inverses.val.length=12 ∧ geometry.line_z.val.length=12
 | _ => True
end NKO_C05
open Lean Elab Tactic
elab "nko_c05_record" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not writer property"
 unless t.getAppArgs.back!.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let t ← getMainTarget
 if t.getAppArgs.back!.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.query then
  evalTactic (← `(tactic| apply NKE_GeometryDomain.returned; apply NKO_Branch.continued <;> assumption))
 else evalTactic (← `(tactic| exact True.intro))
