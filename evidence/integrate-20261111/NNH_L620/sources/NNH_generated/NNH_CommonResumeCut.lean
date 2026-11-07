import NNH_AuthCodeOk
import NNH_ResultBindOk
set_option autoImplicit false
noncomputable section
namespace NNH_CommonResumeCut
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages

theorem source (wr rr : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle)
 (finish : NJJ_Common.Finish) {H : Type} (d : aspis_core.digest.Digest32 H)
 (pub proof ck : Slice U8) (hash : H)
 (success : NJJ_Common.run wr rr merkle finish d pub proof ck hash none=.ok (.Ok ())) :
 ∃ p a,NJJ_Common.resume wr d ck proof pub .S2 hash=.ok (.Ok (p,a)) ∧ a.next=10#usize := by
 unfold NJJ_Common.run at success
 obtain ⟨reply,resume,afterResume⟩ := NNH_ResultBindOk.value _ _ _ success
 cases reply with
 | Err e =>
  with_unfolding_all change Result.ok (.Err e)=Result.ok (.Ok ()) at afterResume
  cases afterResume
 | Ok pair =>
  rcases pair with ⟨p,a⟩
  refine ⟨p,a,resume,?_⟩
  with_unfolding_all change
   (if a.next != NHT_Constants.compact.SPLIT then Result.ok (.Err .Checkpoint) else _)=
    Result.ok (.Ok ()) at afterResume
  cases guard : (a.next != NHT_Constants.compact.SPLIT) with
  | true =>
   rw [guard] at afterResume
   with_unfolding_all change Result.ok (.Err .Checkpoint)=Result.ok (.Ok ()) at afterResume
   cases afterResume
  | false =>
   have equal := bne_eq_false_iff_eq.mp guard
   with_unfolding_all exact equal
#print axioms source
end NNH_CommonResumeCut
