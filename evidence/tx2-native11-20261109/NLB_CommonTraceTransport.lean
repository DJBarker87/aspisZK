import NLB_ProjectedQuestion
set_option autoImplicit false
noncomputable section
namespace NLB_ErrorTransport
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- The whole caller's ordered occurrence log, exact inputs and every non-Merkle
reply are preserved. On a native Merkle Err/cohort fail both prefixes stop there;
no query/flush/finish is invented. Child INTERNAL digest/query histories are
separate fields of the exact child packet, not supplied by this projection. -/
theorem common_trace_transport (wr rr : NP6_StdModel.Reservation)
 (nativeMerkle modelMerkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (child : ∀ proofArg p root,ReplyRel
  (nativeMerkle d proofArg p root 1#usize hash)
  (modelMerkle d proofArg p root 1#usize hash)) :
 observeCommon (run wr rr nativeMerkle finish d pub proof ck hash none)=
 observeCommon (run wr rr modelMerkle finish d pub proof ck hash none) := by
 unfold run
 repeat' first
 | (apply observe_bind_congr; intro)
 | (apply merkle_question; first | apply child | intro; rfl)
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
 | (intro u)
 | rfl
#print common_trace_transport
#print axioms common_trace_transport
end NLB_ErrorTransport
