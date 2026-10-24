import S9Tx2AllFinalPartsV1
import S9PointPartsFoldValuesV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9PointModelFoldValuesV1
open AspisR1Stage2
open AspisR1S9Stage2NativeFinishSlotsV1
open AspisR1S9Tx2AllFinalPartsV1 (PointModel)
open AspisR1S9FactorTableSemanticsV1 (Table Meaning)
open AspisR1S9FinishActualConstructorSlotV1 (fromCtorWeights)
open AspisR1S9ResumeConstructorInputsCanonicalV1 (inputZ inputAlpha)
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
open AspisR1S9RegularPhaseConstructorModelV1 (Means)
open AspisR1S9PointPartsFoldValuesV1 (FivePointFolds five_means_folds)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- Refine ONE supplied PointModel/parts witness, retaining its exact
constructor model, source point producer and both actual alpha reads. -/
theorem point_model_five_fold_values (p : verifier.Prepared)
    (self : AspisR1S9Stage2NativeFinishSlotsV1.Weights) (selected : Slice SW)
    (f : Slice U8) (parts : Array NW 7#usize)
    (hpoint : PointModel p self selected f parts) :
    ∃ (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights) (model : Table),
      self=fromCtorWeights w ∧ Meaning w.factors model ∧
      AspisR1S9StatementFactorOuterSemanticsV1.RowsPrefix w.points model 3 ∧
      AspisR1S9ConstructorV3CompleteFactorSemanticsV1.CircleRows (inputZ p) model ∧
      AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.r0.statement_points (inputAlpha p)=.ok w.points ∧
      ∃ a0 a1 : NW,
        Slice.index_usize (sourceSliceToNative selected) 0#usize=.ok a0 ∧
        Slice.index_usize (sourceSliceToNative selected) 1#usize=.ok a1 ∧
        Means model (decodeNative a0) (decodeNative a1) f parts 1#usize (by decide) 0 ∧
        Means model (decodeNative a0) (decodeNative a1) f parts 2#usize (by decide) 1 ∧
        Means model (decodeNative a0) (decodeNative a1) f parts 3#usize (by decide) 2 ∧
        Means model (decodeNative a0) (decodeNative a1) f parts 5#usize (by decide) 3 ∧
        Means model (decodeNative a0) (decodeNative a1) f parts 6#usize (by decide) 4 ∧
        FivePointFolds model (decodeNative a0) (decodeNative a1) f parts := by
  obtain ⟨w,model,hself,hm,hstatement,hcircle,hproducer,a0,a1,ha0,ha1,h1,h2,h3,h5,h6⟩ := hpoint
  have hf := five_means_folds model (decodeNative a0) (decodeNative a1) f parts
    (by decide) (by decide) (by decide) (by decide) (by decide) h1 h2 h3 h5 h6
  exact ⟨w,model,hself,hm,hstatement,hcircle,hproducer,a0,a1,ha0,ha1,h1,h2,h3,h5,h6,hf⟩
#print axioms point_model_five_fold_values
end AspisR1S9PointModelFoldValuesV1
end
