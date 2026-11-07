import NNH_CommonResumeDomain
set_option autoImplicit false
noncomputable section
namespace NNH_CommonPendingCut
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages

theorem source (wr rr : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle)
 (finish : NJJ_Common.Finish) {H : Type} (d : aspis_core.digest.Digest32 H)
 (pub proof ck : Slice U8) (hash : H)
 (success : NJJ_Common.run wr rr merkle finish d pub proof ck hash none=.ok (.Ok ())) :
 ∃ p a pending,NJJ_Common.resume wr d ck proof pub .S2 hash=.ok (.Ok (p,a)) ∧
 NJJ_Common.pending rr a.weights.deref=.ok (.Ok pending) := by
 unfold NJJ_Common.run at success
 repeat' first
 | (solve | cases success)
 | uncase_result
 | head_reduce success
 | split at success
 all_goals exact ⟨_,_,_,by assumption,by assumption⟩
#print axioms source
end NNH_CommonPendingCut
