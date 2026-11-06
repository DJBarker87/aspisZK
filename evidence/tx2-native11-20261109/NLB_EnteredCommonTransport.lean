import NLB_CommonTraceTransport
import NLB_MerkleGuard
set_option autoImplicit false
noncomputable section
namespace NLB_ErrorTransport
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- C04 transport requires its child only on the domain proved by THAT source
prefix: the SAME proof, resumed Prepared, split accumulator and resume fields.
No all-input native law, child-success, or historical-proof equality is assumed. -/
theorem entered_common_transport (wr rr : NP6_StdModel.Reservation)
 (nativeMerkle modelMerkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (child : ∀ proofArg p root,MerkleDomain wr d ck proof pub hash proofArg p → ReplyRel
  (nativeMerkle d proofArg p root 1#usize hash)
  (modelMerkle d proofArg p root 1#usize hash)) :
 observeCommon (run wr rr nativeMerkle finish d pub proof ck hash none)=
 observeCommon (run wr rr modelMerkle finish d pub proof ck hash none) := by
 unfold run
 repeat' first
 | (apply observe_bind_entered; intro value entered)
 | (apply merkle_question)
 | (apply child; apply at_branch <;> assumption)
 | (apply NKO_Branch.continued <;> assumption)
 | (apply split_start; assumption)
 | (apply NKE_ResumeWidth.returned; apply NKO_Branch.continued <;> assumption)
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
 | (intro u)
 | rfl
#print entered_common_transport
#print axioms entered_common_transport
end NLB_ErrorTransport
