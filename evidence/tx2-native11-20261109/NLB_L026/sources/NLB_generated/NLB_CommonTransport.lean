import NLB_ErrorTransport
import NKE_CommonProgram
set_option autoImplicit false
noncomputable section
namespace NLB_ErrorTransport
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Auxiliary whole-caller Result observation transport. In particular the
native Merkle Err is propagated by the actual caller `?`, with no later suffix.
A complete child packet must additionally supply the ordered effect prefix. -/
theorem common_transport (wr rr : NP6_StdModel.Reservation)
 (nativeMerkle modelMerkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (child : ∀ proofArg p root,ReplyRel
  (nativeMerkle d proofArg p root 1#usize hash)
  (modelMerkle d proofArg p root 1#usize hash)) :
 reject (NJJ_Common.run wr rr nativeMerkle finish d pub proof ck hash none)=
 reject (NJJ_Common.run wr rr modelMerkle finish d pub proof ck hash none) := by
 unfold NJJ_Common.run
 repeat' first
 | (apply bind_congr; intro)
 | (apply question_rel; first | apply child | intro; rfl)
 | (fail_if_no_progress dsimp only [Aeneas.Std.uncurry])
 | split
 | rfl
#print common_transport
#print axioms common_transport
end NLB_ErrorTransport
