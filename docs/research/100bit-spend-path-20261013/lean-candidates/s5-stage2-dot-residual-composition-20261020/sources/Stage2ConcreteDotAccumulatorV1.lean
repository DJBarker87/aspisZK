import Stage2ConcreteDotAdapterV1
import Stage2FinishAccumulator
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1Stage2ConcreteDotAccumulatorV1
open AspisR1Stage2ConcreteDotAdapterV1
open AspisR1FinishDotDecodedProductTrace
open AspisR1FinishRelationCurrent AspisR1FinishDotConcreteOps
local notation "Wide" => AspisWideTower.WideExact
local notation "BaseQ" => AspisV8R15.ExactTowerBase.QM31Exact
local notation "StageE" => AspisR1Stage2.Stage2Finish.E
local notation "StageK" => AspisR1Stage2.Stage2Finish.K

/-- The existing R14 DotLaw is obtained from the concrete kernel and the
individual reader interpretations. No dot equality is an assumption. -/
theorem installed_source_dot_law {W S : Type}
    (stageOps : AspisR1Stage2.Stage2Finish.FinishOps S)
    (kernelOps : FinishOps W PushState)
    (v : AspisR1Stage2.verifier.View) (a : AspisR1Stage2.verifier.Accumulator)
    (d : AspisR1.MatchingSupport.Data Wide) (weights : Fin 64 → BaseQ)
    (hlen : (alloc.vec.Vec.deref a.weights).len.val=64)
    (hfield : ∀ (index : Usize) (value : FinishE) (hi : index.val<64),
      AspisR1CurrentWide.Proof.finishField v.final_message index=ok value →
      AspisR1CurrentWide.Proof.decodeFinish value=d.f ⟨index.val,hi⟩)
    (hweight : ∀ (index : Usize) (value : StageK) (hi : index.val<64),
      Slice.index_usize (alloc.vec.Vec.deref a.weights) index=ok value →
      AspisR1FinishDotReturnedFieldProductV1.finishQMDecoded (toFinishQ value)=weights ⟨index.val,hi⟩) :
    AspisR1.Stage2FinishAccumulator.DotLaw (withSourceDot stageOps kernelOps)
      decodeStage (algebraMap BaseQ Wide) v a d weights := by
  intro value hrun
  exact sourceDot_reader_law kernelOps v.final_message (alloc.vec.Vec.deref a.weights)
    value d.f weights hlen hfield hweight hrun

/-- Successful stage-2 finish yields the residual equation using the actual
kernel arithmetic law. Accumulator, comparison and reader bindings remain
explicit independent obligations. -/
theorem finish_residualBatch_of_reader_interpretation {W S : Type}
    (stageOps : AspisR1Stage2.Stage2Finish.FinishOps S)
    (kernelOps : FinishOps W PushState)
    (compare : AspisR1.Stage2FinishPairing.ComparisonLaw
      (withSourceDot stageOps kernelOps) decodeStage)
    (v : AspisR1Stage2.verifier.View) (p : AspisR1Stage2.verifier.Prepared)
    (a : AspisR1Stage2.verifier.Accumulator)
    (obs : Option (AspisR1Stage2.verifier.Phase → Result Unit))
    (d : AspisR1.MatchingSupport.Data Wide)
    (q : Fin 22 → Fin 262144) (rho : BaseQ) (weights : Fin 64 → BaseQ)
    (hlen : (alloc.vec.Vec.deref a.weights).len.val=64)
    (hfield : ∀ (index : Usize) (value : FinishE) (hi : index.val<64),
      AspisR1CurrentWide.Proof.finishField v.final_message index=ok value →
      AspisR1CurrentWide.Proof.decodeFinish value=d.f ⟨index.val,hi⟩)
    (hweight : ∀ (index : Usize) (value : StageK) (hi : index.val<64),
      Slice.index_usize (alloc.vec.Vec.deref a.weights) index=ok value →
      AspisR1FinishDotReturnedFieldProductV1.finishQMDecoded (toFinishQ value)=weights ⟨index.val,hi⟩)
    (inv : AspisR1.Stage2FinishAccumulator.Invariant decodeStage
      (algebraMap BaseQ Wide) a d q rho weights)
    (two : (withSourceDot stageOps kernelOps).folds p.variant=ok 2#usize)
    (hrun : AspisR1Stage2.Stage2Finish.verifier.finishRelationWithOps
      (withSourceDot stageOps kernelOps) v p a obs=ok (.Ok ())) :
    ∑ j : Fin 22,(algebraMap BaseQ Wide rho)^j.val *
      AspisR1.QueryResidualBridge.residuals d q j=0 := by
  exact AspisR1.Stage2FinishAccumulator.finish_residualBatch
    (withSourceDot stageOps kernelOps) decodeStage compare (algebraMap BaseQ Wide)
    v p a obs d q rho weights
    (installed_source_dot_law stageOps kernelOps v a d weights hlen hfield hweight)
    inv two hrun

#print axioms finish_residualBatch_of_reader_interpretation
#print axioms installed_source_dot_law
end AspisR1Stage2ConcreteDotAccumulatorV1
end
