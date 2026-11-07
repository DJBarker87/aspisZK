import NNH_CommonPendingCut
set_option autoImplicit false
noncomputable section
namespace NNH_CommonReservation
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages

theorem source (wr rr : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle)
 (finish : NJJ_Common.Finish) {H : Type} (d : aspis_core.digest.Digest32 H)
 (pub proof ck : Slice U8) (hash : H) (size : ck.val.length=1768)
 (success : NJJ_Common.run wr rr merkle finish d pub proof ck hash none=.ok (.Ok ())) :
 NJC_FilledClause.reserved rr=true := by
 obtain ⟨p,a,pending,resume,pending_ok⟩ := NNH_CommonPendingCut.source wr rr merkle finish d pub proof ck hash success
 obtain ⟨p0,a0,resume0,domain,next⟩ := NNH_CommonResumeDomain.source wr rr merkle finish d pub proof ck hash size success
 have same : (p,a)=(p0,a0) := core.result.Result.Ok.inj (Result.ok.inj (resume.symm.trans resume0))
 cases same
 unfold NJJ_Common.pending at pending_ok
 rw [NHV_PendingPacket.source _ _ domain.width] at pending_ok
 cases flag : NJC_FilledClause.reserved rr with
 | false => rw [flag] at pending_ok; cases pending_ok
 | true => rfl

#print axioms source
end NNH_CommonReservation
