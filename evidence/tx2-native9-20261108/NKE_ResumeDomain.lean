import NJU_ResumeRoot
import NJU_CommonObserved
import NJR_FinishPrepared
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeDomain
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- Internal inversion at the SAME source bind. Error, fail and div cannot
supply a success payload; this is never an extra positive-root premise. -/
theorem action_ok {A : Type} (m : Result (core.result.Result A verifier.Error)) (value : A)
 (run : NHT_ResultPort.action m=ok (.Ok value)) : m=ok (.Ok value) := by
 cases m with
 | fail e => cases run
 | div => cases run
 | ok reply =>
  cases reply with
  | Err e => cases run
  | Ok a =>
   have same := core.result.Result.Ok.inj (Result.ok.inj run)
   cases same;rfl

theorem returned (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (p : verifier.Prepared) (a : verifier.Accumulator) (ckSize : ck.val.length=1768)
 (entered : NJJ_Common.resume reservation d ck proof pub .S2 hash=ok (.Ok (p,a))) :
 NID_ResumeFields.Domain p a := by
 unfold NJJ_Common.resume at entered
 rw [NJC_ResumeCalls.clause] at entered
 have same := action_ok _ _ entered
 exact NID_ResumeFields.returned (NJC_FilledClause.reserved reservation)
  (NJC_ResumeCalls.digest d) ck proof pub hash p a ckSize same
#print axioms action_ok
#print axioms returned
end NKE_ResumeDomain
