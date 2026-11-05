import NHT_FinishRelationModel
set_option autoImplicit false
noncomputable section
namespace NHT_FinishChain
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody NGM_FinishControl NHQ_FinishRelationModel
variable {W : Type}
abbrev PairPacket (W : Type) := W → Slice E → Slice U8 → E → Result (R E)

def afterWeights (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (dotWeights : Slice NHE_DotBody.NQ) (pair : PairPacket W)
 (folds : Usize) (claim : E) (reply : R W) : Result (R Unit) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf with
 | .Continue weights =>
   let alpha ← core.array.Array.index (core.ops.index.IndexSlice
     (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end» := folds}
   let r ← pair weights alpha v.final_message p.kappa
   NHT_FinishRelationModel.afterPairPacket ops v p a obs dotWeights claim r
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual

theorem weights_frame (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (ws : Slice NHE_DotBody.NQ) (pair : PairPacket W) (folds : Usize) (claim : E)
 (reply : R W)
 (pair_law : ∀ weights, reply=.Ok weights → ∀ alpha,
   core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=folds}=ok alpha →
   NHT_FinishRelationModel.PairLaw ops v p weights alpha
     (pair weights alpha v.final_message p.kappa))
 (tail : ∀ r, afterPairReply ops v p a obs claim r =
   NHT_FinishRelationModel.afterPairPacket ops v p a obs ws claim r) :
 afterWeightsReply ops v p a obs folds claim reply =
 afterWeights ops v p a obs ws pair folds claim reply := by
 cases reply with
 | Err e => rfl
 | Ok weights =>
   unfold afterWeightsReply afterWeights
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
   apply NHT_BindOn.reached
   intro alpha same
   rw [pair_law weights rfl alpha same]
   apply NHT_BindOn.reached
   intro r _
   exact tail r

def afterRound (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (ws : Slice NHE_DotBody.NQ) (pair : PairPacket W)
 (folds : Usize) (reply : R E) : Result (R Unit) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf with
 | .Continue claim =>
   let weights ← ops.op3 p.variant p.semantic_alpha p.z
   afterWeights ops v p a obs ws pair folds claim weights
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual

theorem round_tail (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (ws : Slice NHE_DotBody.NQ) (pair : PairPacket W)
 (folds : Usize) (reply : R E)
 (next : ∀ claim weights,
   ops.op3 p.variant p.semantic_alpha p.z=ok weights →
   afterWeightsReply ops v p a obs folds claim weights =
     afterWeights ops v p a obs ws pair folds claim weights) :
 afterRoundReply ops v p a obs folds reply =
 afterRound ops v p a obs ws pair folds reply := by
 cases reply with
 | Err e => rfl
 | Ok claim =>
   unfold afterRoundReply afterRound
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
   apply NHT_BindOn.reached
   intro weights same
   exact next claim weights same
#print axioms weights_frame
#print axioms round_tail
end NHT_FinishChain
