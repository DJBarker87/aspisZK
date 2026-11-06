import NKO_C07Core
set_option autoImplicit false
noncomputable section
namespace NLB_C04Domain
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- C04 receives THAT resumed Prepared and current proof; its accumulator
passed the split gate. No successful Merkle or history premise is required. -/
def Holds (wr : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H) : Event → Prop
 | .merkle proofArg p _ _ => proofArg=proof ∧ ∃ a,
   NJJ_Common.resume wr d ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
   a.next=10#usize ∧ NID_ResumeFields.Domain p a
 | _ => True
end NLB_C04Domain
open Lean Elab Tactic
elab "nlb_c04_record" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not writer property"
 unless t.getAppArgs.back!.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let t ← getMainTarget
 if t.getAppArgs.back!.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.merkle then
  evalTactic (← `(tactic| exact ⟨rfl,$(mkIdent `a),$(mkIdent `entered),$(mkIdent `start),$(mkIdent `fields)⟩))
 else evalTactic (← `(tactic| exact True.intro))
