import NKE_CommonDomain
set_option autoImplicit false
noncomputable section
namespace NKO_C02
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- A powers occurrence retains the producer of its gamma, rather than an
independently chosen canonical value. This is a source-domain property only. -/
def Holds (wr : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H) : Event → Prop
 | .powers gamma _ => ∃ p a,
   NJJ_Common.resume wr d ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
   gamma=p.gamma ∧ NID_ResumeFields.Domain p a
 | _ => True
end NKO_C02
open Lean Elab Tactic
elab "nko_c02_record" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not writer property"
 let m := t.getAppArgs.back!
 unless m.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let t ← getMainTarget
 let event := t.getAppArgs.back!
 if event.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.powers then
  evalTactic (← `(tactic| exact ⟨$(mkIdent `p),$(mkIdent `a),$(mkIdent `entered),rfl,$(mkIdent `fields)⟩))
 else evalTactic (← `(tactic| exact True.intro))
