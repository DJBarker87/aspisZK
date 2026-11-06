import NKO_C05Core
import NKO_C06Result
set_option autoImplicit false
noncomputable section
namespace NKO_C07
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
def Holds (wr : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H) : Event → Prop
 | .query proofArg p a g _ pending _ =>
   proofArg=proof ∧ NJJ_Common.resume wr d ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
   a.next=10#usize ∧ NID_ResumeFields.Domain p a ∧ pending=NFW_QueryResume.pending a ∧ NHT_PacketOps.powers 29#usize p.gamma=ok g
 | _ => True
end NKO_C07
open Lean Elab Tactic
elab "nko_c07_record" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not writer property"
 unless t.getAppArgs.back!.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let t ← getMainTarget
 if t.getAppArgs.back!.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.query then
  evalTactic (← `(tactic| refine ⟨rfl,$(mkIdent `entered),$(mkIdent `start),$(mkIdent `fields),?_,?_⟩))
  evalTactic (← `(tactic| apply NKO_C06.pending_eq _ _ $(mkIdent `width); apply NKO_Branch.continued <;> assumption))
  evalTactic (← `(tactic| assumption))
 else evalTactic (← `(tactic| exact True.intro))
