import NNH_CommonResumeCut
set_option autoImplicit false
noncomputable section
namespace NNH_CommonResumeDomain
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages

theorem source (wr rr : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle)
 (finish : NJJ_Common.Finish) {H : Type} (d : aspis_core.digest.Digest32 H)
 (pub proof ck : Slice U8) (hash : H) (size : ck.val.length=1768)
 (success : NJJ_Common.run wr rr merkle finish d pub proof ck hash none=.ok (.Ok ())) :
 ∃ p a,NJJ_Common.resume wr d ck proof pub .S2 hash=.ok (.Ok (p,a)) ∧
 NID_ResumeFields.Domain p a ∧ a.next=10#usize := by
 obtain ⟨p,a,resume,next⟩ := NNH_CommonResumeCut.source wr rr merkle finish d pub proof ck hash success
 refine ⟨p,a,resume,?_,next⟩
 have raw := NHT_ResultSuccess.source _ _ resume
 rw [NJC_ResumeCalls.clause] at raw
 exact NID_ResumeFields.returned (NJC_FilledClause.reserved wr) (NJC_ResumeCalls.digest d) ck proof pub hash p a size raw
#print axioms source
end NNH_CommonResumeDomain
