import S9ConstructorV3CompleteFactorSemanticsV1
import S9ConstructorTableNativeTensorV1
import S9ConstructorNativeReceiverCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualConstructorNativeTensorV1
open AspisR1S9FinishActualConstructorSlotV1
open AspisR1S9FactorTableSemanticsV1
open AspisR1S9ConstructorV3CompleteFactorSemanticsV1
open AspisR1S9StatementFactorOuterSemanticsV1
abbrev NQ := AspisR1S9ProductionPairCutV1.aspis_core.field.QM31
abbrev CW := AspisR1S9ActualWeightsNewBoxNewV3.Weights
abbrev nativeDecode := AspisR1S9ActualTensorArithmeticV1.decode
abbrev highProduct := AspisR1S9ActualTensorOuterSemanticsV1.highProduct

variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- The concrete constructor and this same receiver's accepted native tensor
call supply their complete table/model and canonicality internally. No
independent factor meaning, native factor canonicality or successful child
constructor/phase call is assumed. Input canonicality is supplied by the
existing same-resume current-decoder path in the enclosing caller.
Source normalization, Box/allocation and actual caller/runtime/artifact
correspondence remain separate release obligations. -/
theorem actual_constructor_native_tensor_success_complete
    (variant : AspisR1FinishRelationCurrent.transport.Variant)
    (alpha : Array AspisR1FinishRelationCurrent.aspis_core.field.QM31 10#usize)
    (z : Array AspisR1FinishRelationCurrent.aspis_core.circle.SecureCirclePoint 2#usize)
    (self : Weights) (k : Usize) (input out : Slice NQ)
    (halpha : AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1.VectorCanonical
      (mapArray toCtorQM alpha))
    (hz : AspisR1S9ConstructorV3PointScanBodyCanonicalV1.PointsCanonical (mapArray toCtorPoint z))
    (hk : k.val<5)
    (hnew : actualNewWeightsSlot variant alpha z = .ok (.Ok self))
    (htensor : AspisR1S9ProductionPairCutV1.weights.Weights.tensor self k 2#usize input=.ok out) :
    ∃ (w : CW) (model : Table),
      AspisR1S9ActualWeightsNewBoxNewV3.weights_new (toCtorVariant variant)
        (mapArray toCtorQM alpha) (mapArray toCtorPoint z)=.ok (.Ok w) ∧
      self=fromCtorWeights w ∧ Meaning w.factors model ∧ RowsPrefix w.points model 3 ∧
      CircleRows (mapArray toCtorPoint z) model ∧
      AspisR1S9TensorIndexedMeaningV1.MeaningOn nativeDecode
        (highProduct (model k.val)) (fun i => i<64) out := by
  obtain ⟨w,hsource,hself⟩ := actualNewWeightsSlot_success variant alpha z self hnew
  obtain ⟨model,hm,hstatement,hcircle,hpoints,hvariant,hextra⟩ :=
    constructor_success_complete_factor_semantics (toCtorVariant variant)
      (mapArray toCtorQM alpha) (mapArray toCtorPoint z) w halpha hz hsource
  have hc := (AspisR1S9ConstructorNativeReceiverCanonicalV1.actual_constructor_slot_success_receiver_canonical
    variant alpha z self halpha hz hnew).1
  have hc' : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtorWeights w) := by
    rw [←hself]
    exact hc
  have ht' : AspisR1S9ProductionPairCutV1.weights.Weights.tensor
      (fromCtorWeights w) k 2#usize input=.ok out := by
    rw [←hself]
    exact htensor
  have hresult := AspisR1S9ConstructorTableNativeTensorV1.native_tensor_success_table
    w model hm hc' k hk input out ht'
  exact ⟨w,model,hsource,hself,hm,hstatement,hcircle,hresult⟩

#print axioms actual_constructor_native_tensor_success_complete
end AspisR1S9ActualConstructorNativeTensorV1
