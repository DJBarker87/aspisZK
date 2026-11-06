import NKO_C03Window
import NKE_Entered
set_option autoImplicit false
noncomputable section
namespace NKO_C03
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
def Holds (proof : Slice U8) : Event → Prop
 | .inactive bytes _ => select proof=ok bytes
 | _ => True
end NKO_C03
open Lean Elab Tactic
elab "nko_c03_bind" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not writer property"
 unless t.getAppArgs.back!.isAppOf ``Bind.bind do throwError "not bind"
 evalTactic (← `(tactic| apply NKE_Entered.bind_all))
elab "nko_c03_record" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not writer property"
 unless t.getAppArgs.back!.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let t ← getMainTarget
 if t.getAppArgs.back!.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.inactive then
  evalTactic (← `(tactic| assumption))
 else evalTactic (← `(tactic| exact True.intro))
