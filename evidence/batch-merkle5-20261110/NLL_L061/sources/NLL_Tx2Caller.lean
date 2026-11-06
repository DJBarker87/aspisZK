import NLL_ResumeQueries
import NKE_CommonDomain
import NKE_ResumeDomain
set_option autoImplicit false
noncomputable section
namespace NLL_Tx2Caller
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved

theorem resumed (reservation : NP6_StdModel.Reservation) {X : Type}
 (d : aspis_core.digest.Digest32 X) (ck proof pub : Slice U8) (hash : X)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (entered : NJJ_Common.resume reservation d ck proof pub .S2 hash=ok (.Ok (p,a))) :
 ∀ j,j<22 → p.queries.val[j]!.val<262144 := by
 unfold NJJ_Common.resume at entered
 rw [NJC_ResumeCalls.clause] at entered
 have same:=NKE_ResumeDomain.action_ok _ _ entered
 change AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved reservation))
   (NJC_ResumeCalls.digest d) ck proof pub .S2 hash=ok (.Ok (p,a)) at same
 exact NLL_ResumeQueries.returned _ _ ck proof pub hash p a same

/-- Source occurrence property for the actual TX2 C04 site. This is an
intermediate carrier theorem, not a proof of the outer native parent. -/
def Holds (wr : NP6_StdModel.Reservation) {X : Type}
 (d : aspis_core.digest.Digest32 X) (ck proof pub : Slice U8) (hash : X) : Event → Prop
 | .merkle enteredProof p _ _ => enteredProof=proof ∧ ∃ a,
   NJJ_Common.resume wr d ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
   ∀ j,j<22 → p.queries.val[j]!.val<262144
 | _ => True
end NLL_Tx2Caller
open Lean Elab Tactic
elab "nll_merkle_record" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not event property"
 let m := t.getAppArgs.back!
 unless m.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let t ← getMainTarget
 let event := t.getAppArgs.back!
 if event.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.merkle then
  evalTactic (← `(tactic| exact ⟨rfl,$(mkIdent `a),$(mkIdent `entered),$(mkIdent `canonical)⟩))
 else evalTactic (← `(tactic| exact True.intro))
namespace NLL_Tx2Caller
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved

theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X) :
 NKE_EventAll.Holds (Holds wr d ck proof pub hash) (run wr rr merkle finish d pub proof ck hash none) := by
 unfold NJU_CommonObserved.run
 apply NKE_Entered.bind_all
 · apply NKE_EventAll.record_all
   exact True.intro
 · intro reply entered
   cases reply with
   | Err error =>
     simp only [core.result.Result.Insts.CoreOpsTry.branch,NKE_Entered.lift_ok]
     exact NKE_EventAll.lift_all _ _
   | Ok pair =>
     rcases pair with ⟨p,a⟩
     have canonical:=resumed wr d ck proof pub hash p a entered
     simp only [core.result.Result.Insts.CoreOpsTry.branch,NKE_Entered.lift_ok]
     by_cases wrong : (a.next != NHT_Constants.compact.SPLIT)=true
     · rw [if_pos wrong]
       exact NKE_EventAll.lift_all _ _
     · rw [if_neg wrong]
       apply NKE_EventAll.bind_all
       repeat' first
       | nke_zeta
       | nke_bind
       | nke_intro
       | nke_lift
       | nke_pure
       | nll_merkle_record
       | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
       | split

set_option pp.proofs false
#print source
#print axioms resumed
#print axioms source
end NLL_Tx2Caller
end
