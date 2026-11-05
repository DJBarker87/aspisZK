import NHT_FinishComplete
import NHT_RoundOutput
set_option autoImplicit false
noncomputable section
namespace NHT_FinishCaller
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody NGM_FinishControl NHQ_FinishRelationModel NHT_FinishChain
variable {W : Type}
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
 (native_round1 : ∀ claim, LPi_FieldValues.canonE (FIo_Install.toE claim) →
   ops.op5 v.round1 alpha1 claim 1#usize =
   Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r) v.round1 alpha1 claim 1#usize)
 (accumulator : NGM_FinishDomain.AccumulatorDomain a)
 (native_dot : ops.op4 v.final_message a.weights.deref=
   SAG_DotClosed.source v.final_message a.weights.deref)
 (newPacket : Result (R W))
 (NHM_new : ops.op3 p.variant p.semantic_alpha p.z=newPacket)
 (pair : PairPacket W)
 (NHM_pair : ∀ weights, ops.op3 p.variant p.semantic_alpha p.z=ok (.Ok weights) →
   ∀ alpha, core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=2#usize}=ok alpha →
   NHT_FinishRelationModel.PairLaw ops v p weights alpha
     (pair weights alpha v.final_message p.kappa)) :
 Port3_NativeFinishBody.verifier.finish_relation ops v p a obs =
 NHT_FinishRun.run (NHT_FinishNewPacket.installed ops newPacket) v p a obs (NHQ_WeightPort.weights a.weights.deref) pair alpha0 alpha1 := by
 apply NHT_FinishComplete.source ops r v p a obs alpha0 alpha1 index0 index1 ca0 ca1
   folds native_round0
 · intro claim returned
   exact native_round1 claim (NHT_RoundOutput.canonical v.round0 alpha0 p.claim claim ca0 returned)
 · exact NHQ_FinishFrames.dot_width a accumulator
 · exact (NHQ_WeightPort.same a.weights.deref).symm
 · exact native_dot
 · exact NHM_new
 · exact NHM_pair
#print axioms source
end NHT_FinishCaller
