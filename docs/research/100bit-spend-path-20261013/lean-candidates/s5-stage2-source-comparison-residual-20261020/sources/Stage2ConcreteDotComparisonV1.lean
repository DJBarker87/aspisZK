import Stage2ConcreteDotAccumulatorV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1Stage2ConcreteDotComparisonV1
open AspisR1Stage2ConcreteDotAdapterV1
open AspisR1FinishDotDecodedProductTrace
open AspisR1FinishRelationCurrent AspisR1FinishDotConcreteOps
local notation "StageE" => AspisR1Stage2.Stage2Finish.E

def sourceNe (x y : StageE) : Result Bool := do
  let equal ← AspisR1CurrentWide.Proof.finishEq (toFinishE x) (toFinishE y)
  ok (!equal)

theorem sourceNe_false_decode (x y : StageE) (h : sourceNe x y=ok false) :
    decodeStage x=decodeStage y := by
  unfold sourceNe at h
  cases he : AspisR1CurrentWide.Proof.finishEq (toFinishE x) (toFinishE y) with
  | fail e => simp only [he,bind_tc_fail] at h; cases h
  | div => simp only [he,bind_tc_div] at h; cases h
  | ok equal =>
    cases equal with
    | false => simp only [he,bind_tc_ok,Bool.not_false] at h; cases h
    | true =>
      exact congrArg AspisR1CurrentWide.Proof.decodeFinish
        (AspisR1CurrentWide.Proof.finish_eq_success_true (toFinishE x) (toFinishE y) he)

def withSourceDotNe {W S : Type} (stageOps : AspisR1Stage2.Stage2Finish.FinishOps S)
    (kernelOps : FinishOps W PushState) : AspisR1Stage2.Stage2Finish.FinishOps S :=
  withSourceDot {stageOps with ne:=sourceNe} kernelOps

theorem installed_source_comparison_law {W S : Type}
    (stageOps : AspisR1Stage2.Stage2Finish.FinishOps S)
    (kernelOps : FinishOps W PushState) :
    AspisR1.Stage2FinishPairing.ComparisonLaw (withSourceDotNe stageOps kernelOps) decodeStage := by
  intro x y h
  exact sourceNe_false_decode x y h

structure ReaderMeaning (fm : Slice U8) (ws : Slice AspisR1Stage2.Stage2Finish.K)
    (f : Fin 64 → AspisWideTower.WideExact)
    (weights : Fin 64 → AspisV8R15.ExactTowerBase.QM31Exact) : Prop where
  length : ws.len.val=64
  field : ∀ (index : Usize) (value : FinishE) (hi : index.val<64),
    AspisR1CurrentWide.Proof.finishField fm index=ok value →
    AspisR1CurrentWide.Proof.decodeFinish value=f ⟨index.val,hi⟩
  weight : ∀ (index : Usize) (value : AspisR1Stage2.Stage2Finish.K) (hi : index.val<64),
    Slice.index_usize ws index=ok value →
    AspisR1FinishDotReturnedFieldProductV1.finishQMDecoded (toFinishQ value)=weights ⟨index.val,hi⟩

/-- Source equality supplies the comparison law; no separate comparison
correctness or complete dot equation is a premise. -/
theorem finish_residualBatch_with_source_dot_ne {W S : Type}
    (stageOps : AspisR1Stage2.Stage2Finish.FinishOps S)
    (kernelOps : FinishOps W PushState)
    (v : AspisR1Stage2.verifier.View) (p : AspisR1Stage2.verifier.Prepared)
    (a : AspisR1Stage2.verifier.Accumulator)
    (obs : Option (AspisR1Stage2.verifier.Phase → Result Unit))
    (d : AspisR1.MatchingSupport.Data AspisWideTower.WideExact)
    (q : Fin 22 → Fin 262144) (rho : AspisV8R15.ExactTowerBase.QM31Exact)
    (weights : Fin 64 → AspisV8R15.ExactTowerBase.QM31Exact)
    (reader : ReaderMeaning v.final_message (alloc.vec.Vec.deref a.weights) d.f weights)
    (inv : AspisR1.Stage2FinishAccumulator.Invariant decodeStage
      (algebraMap AspisV8R15.ExactTowerBase.QM31Exact AspisWideTower.WideExact) a d q rho weights)
    (two : (withSourceDotNe stageOps kernelOps).folds p.variant=ok 2#usize)
    (hrun : AspisR1Stage2.Stage2Finish.verifier.finishRelationWithOps
      (withSourceDotNe stageOps kernelOps) v p a obs=ok (.Ok ())) :
    ∑ j : Fin 22,(algebraMap AspisV8R15.ExactTowerBase.QM31Exact AspisWideTower.WideExact rho)^j.val *
      AspisR1.QueryResidualBridge.residuals d q j=0 := by
  exact AspisR1Stage2ConcreteDotAccumulatorV1.finish_residualBatch_of_reader_interpretation
    {stageOps with ne:=sourceNe} kernelOps
    (installed_source_comparison_law stageOps kernelOps)
    v p a obs d q rho weights reader.length reader.field reader.weight inv two hrun

#print axioms finish_residualBatch_with_source_dot_ne
#print axioms sourceNe_false_decode
#print axioms installed_source_comparison_law
end AspisR1Stage2ConcreteDotComparisonV1
end
