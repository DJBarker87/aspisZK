import NHT_FinishRun
set_option autoImplicit false
noncomputable section
namespace NHT_FinishCompose
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody NGM_FinishControl NHQ_FinishRelationModel NHT_FinishChain
variable {W : Type}
/-- Full S2 frame-chain refinement. Only reached NEW outputs and their actual
alpha slice require NHM's pair law. Every CLOSED round/dot law is instantiated
here from its packet and primitive carrier/domain facts. -/
theorem source (ops : Ops W) (r : NP6_StdModel.Reservation)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit))
 (alpha0 alpha1 : E)
 (index0 : Array.index_usize p.alpha 0#usize=ok alpha0)
 (index1 : Array.index_usize p.alpha 1#usize=ok alpha1)
 (ca0 : LPi_FieldValues.canonE (FIo_Install.toE alpha0))
 (ca1 : LPi_FieldValues.canonE (FIo_Install.toE alpha1))
 (folds : ops.op6 p.variant=ok 2#usize)
 (native_round0 : ops.op5 v.round0 alpha0 p.claim 0#usize =
   Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r) v.round0 alpha0 p.claim 0#usize)
 (native_round1 : ∀ claim, ops.op5 v.round1 alpha1 claim 1#usize =
   Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r) v.round1 alpha1 claim 1#usize)
 (ws : Slice NHE_DotBody.NQ) (width : ws.val.length≤64)
 (same : a.weights.deref=SAG_DotAdapter.mapSlice NHE_DotRead.stageQ ws)
 (native_dot : ops.op4 v.final_message a.weights.deref=
   SAG_DotClosed.source v.final_message a.weights.deref)
 (pair : PairPacket W)
 (NHM_pair : ∀ weights, ops.op3 p.variant p.semantic_alpha p.z=ok (.Ok weights) →
   ∀ alpha, core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=2#usize}=ok alpha →
   NHT_FinishRelationModel.PairLaw ops v p weights alpha
     (pair weights alpha v.final_message p.kappa)) :
 Port3_NativeFinishBody.verifier.finish_relation ops v p a obs =
 NHT_FinishRun.run ops v p a obs ws pair alpha0 alpha1 := by
 apply NHT_FinishRun.source ops v p a obs ws pair alpha0 alpha1 index0
 · exact native_round0.trans (NHT_RoundPacket.source r v.round0 alpha0 p.claim 0#usize ca0 (by decide)).symm
 · intro reply
   apply NHT_FinishRun.first_frame ops v p a obs ws pair alpha1 folds index1
   · intro claim
     exact (native_round1 claim).trans (NHT_RoundPacket.source r v.round1 alpha1 claim 1#usize ca1 (by decide)).symm
   · intro roundReply
     apply NHT_FinishChain.round_tail
     intro claim weights reached
     apply NHT_FinishChain.weights_frame
     · intro w returned alpha indexed
       subst weights
       exact NHM_pair w reached alpha indexed
     · intro pairReply
       exact NHT_FinishRelationModel.after_pair ops v p a obs ws width same native_dot claim pairReply
   · exact reply
#print axioms source
end NHT_FinishCompose
