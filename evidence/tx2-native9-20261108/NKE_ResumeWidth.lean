import NKE_ResumeDomain
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeWidth
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- Width is derived inside the entered resume branch, including malformed
checkpoint rejection; no checkpoint-length hypothesis is added to a root. -/
theorem checkpoint (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (entered : NJJ_Common.resume reservation d ck proof pub .S2 hash=ok (.Ok (p,a))) :
 ck.val.length=1768 := by
 unfold NJJ_Common.resume at entered
 rw [NJC_ResumeCalls.clause] at entered
 have same := NKE_ResumeDomain.action_ok _ _ entered
 change verifier.resumeWithOps (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved reservation))
  (NJC_ResumeCalls.digest d) ck proof pub .S2 hash=ok (.Ok (p,a)) at same
 rw [←NIY_ResumePort.source] at same
 cases run : NIL_FreshOps.resume (NJC_FilledClause.reserved reservation)
  (NJC_ResumeCalls.digest d) ck proof pub .S2 hash with
 | fail e => rw [run] at same;cases same
 | div => rw [run] at same;cases same
 | ok reply =>
  cases reply with
  | Err e => rw [run] at same;cases same
  | Ok pair =>
   rcases pair with ⟨freshP,freshA⟩
   exact NJC_QueryOccurrence.checkpoint_size (NJC_FilledClause.reserved reservation)
    (NJC_ResumeCalls.digest d) ck proof pub hash freshP freshA run

theorem returned (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (entered : NJJ_Common.resume reservation d ck proof pub .S2 hash=ok (.Ok (p,a))) :
 NID_ResumeFields.Domain p a :=
 NKE_ResumeDomain.returned reservation d ck proof pub hash p a
  (checkpoint reservation d ck proof pub hash p a entered) entered
#print axioms checkpoint
#print axioms returned
end NKE_ResumeWidth
