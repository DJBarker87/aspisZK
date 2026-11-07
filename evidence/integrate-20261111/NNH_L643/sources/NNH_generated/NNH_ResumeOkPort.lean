import NNH_CommonResumeDomain
set_option autoImplicit false
noncomputable section
namespace NNH_ResumeOkPort
open Aeneas Aeneas.Std AspisR1 VTop_Stages

theorem value (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (success : NJJ_Common.resume reservation d ck proof pub .S2 hash=.ok (.Ok (p,a))) :
 Port4A_ReaderInstall.reader (NJC_FilledClause.reserved reservation) d ck proof pub .S2 hash=.ok (.Ok (p,a)) := by
 have raw := NHT_ResultSuccess.source _ _ success
 rw [NJC_ResumeCalls.clause] at raw
 unfold NJC_ResumeCalls.cohort at raw
 rw [Port4A_ReaderInstall.reference_eq]
 unfold Port3_CheckpointInstall.reader
 rw [raw]
 rfl
#print axioms value
end NNH_ResumeOkPort
