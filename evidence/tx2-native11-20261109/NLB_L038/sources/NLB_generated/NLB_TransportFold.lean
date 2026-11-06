import NLB_TargetSteps
import NLB_ResumePacket
import NLB_CommonTraceTransport
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Parameterized semantic parent fold: full resume observed-run packet at
SAME inputs, native Merkle full Result kept, and explicit (bb)/(bc) rejection
transport to the model. C04's INTERNAL digest/frame packet is still OPEN and
is not supplied by the ReplyRel projection. This is NOT a TX2:065 row root. -/
theorem transport_fold (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (nativeResume : NLB_ResumePacket.Native) (nativeMerkle modelMerkle : Merkle)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (resumePacket : NLB_ResumePacket.At nativeResume wr d ck proof pub hash)
 (merkleReply : ∀ proofArg p root,NLB_ErrorTransport.ReplyRel
  (nativeMerkle d proofArg p root 1#usize hash)
  (modelMerkle d proofArg p root 1#usize hash))
 (headlineSize : proof.val.length=57607)
 (observe : NKE_QueryInput.Args → QueryObservation)
 (cuts : QueryCuts wr rr fr nativeMerkle d pub proof ck hash observe)
 (before : List Event) :
 let w:=queryWindow (window rr fr loc (NLB_ResumePacket.action nativeResume wr) nativeMerkle d hash) observe
 let p:=NKE_CommonProgram.run wr rr nativeMerkle (finish fr) d pub proof ck hash none
 G w p before=.done (NJJ_Common.run wr rr nativeMerkle (finish fr) d pub proof ck hash none)
  (before++(run wr rr nativeMerkle (finish fr) d pub proof ck hash none).events) ∧
 NLB_ErrorTransport.observeCommon (run wr rr nativeMerkle (finish fr) d pub proof ck hash none)=
 NLB_ErrorTransport.observeCommon (run wr rr modelMerkle (finish fr) d pub proof ck hash none) := by
 dsimp only
 constructor
 · have localSteps : ∀ e∈(NKE_Free.eval (NKE_CommonProgram.run wr rr nativeMerkle (finish fr) d pub proof ck hash none)).events,
    queryWindow (window rr fr loc (NLB_ResumePacket.action nativeResume wr) nativeMerkle d hash) observe e=e := by
    rw [NKE_CommonEval.source]
    exact target_steps wr rr fr loc (NLB_ResumePacket.action nativeResume wr) nativeMerkle d pub proof ck hash
     (NLB_ResumePacket.projection nativeResume wr d ck proof pub hash resumePacket) headlineSize observe cuts
   have folded:=events_from_cuts _ (NKE_CommonProgram.run wr rr nativeMerkle (finish fr) d pub proof ck hash none) before localSteps
   rw [NKE_CommonEval.source,NJU_CommonObserved.source] at folded
   exact folded
 · exact NLB_ErrorTransport.common_trace_transport wr rr nativeMerkle modelMerkle (finish fr) d pub proof ck hash merkleReply
#print transport_fold
#print axioms transport_fold
end NLB_Parent
