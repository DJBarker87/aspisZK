import S9CurrentReaderNativeProducersV1
import S9ActualConstructorNativeTensorV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CurrentResumeFinishNativeTensorV1
open AspisR1S9ResumeFinishNativePairBindingV1
open AspisR1S9ActualConstructorNativeTensorV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- SAME current-reader resume and concrete finish supply canonical constructor
inputs and its SAME receiver. The tensor implication concerns that receiver;
its accepted execution remains explicit until native Pair call reachability
is proved. No raw/caller/Box/runtime or artifact refinement is asserted. -/
theorem current_resume_finish_same_constructor_tensor_semantics {D H : Type}
    (readerOps : AspisR1Stage2.ResumeOps)
    (digest : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (hash : H)
    (p : AspisR1Stage2.verifier.Prepared) (acc : AspisR1Stage2.verifier.Accumulator)
    (ops : AspisR1FinishRelationCurrent.FinishOps Weights D)
    (v : AspisR1FinishRelationCurrent.verifier.View)
    (a : AspisR1FinishRelationCurrent.verifier.Accumulator)
    (obs : Option (AspisR1FinishRelationCurrent.verifier.Phase → Result Unit))
    (hresume : AspisR1Stage2.verifier.resumeWithOps
      (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders readerOps)
      digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash = .ok (.Ok (p,acc)))
    (hfinish : AspisR1FinishRelationCurrent.verifier.finish_relation
      (AspisR1S9FinishActualConstructorSlotV1.installActualConstructor ops)
      v (stagePrepared p) a obs = .ok (.Ok ())) :
    ∃ (self : Weights),
      AspisR1S9FinishActualConstructorSlotV1.actualNewWeightsSlot
        (stagePrepared p).variant (stagePrepared p).semantic_alpha (stagePrepared p).z = .ok (.Ok self) ∧
      ∀ (k : Usize) (input out : Slice NQ), k.val < 5 →
        AspisR1S9ProductionPairCutV1.weights.Weights.tensor self k 2#usize input = .ok out →
        ∃ (w : CW) (model : AspisR1S9FactorTableSemanticsV1.Table),
          AspisR1S9ActualWeightsNewBoxNewV3.weights_new
            (AspisR1S9FinishActualConstructorSlotV1.toCtorVariant (stagePrepared p).variant)
            (AspisR1S9FinishActualConstructorSlotV1.mapArray
              AspisR1S9FinishActualConstructorSlotV1.toCtorQM (stagePrepared p).semantic_alpha)
            (AspisR1S9FinishActualConstructorSlotV1.mapArray
              AspisR1S9FinishActualConstructorSlotV1.toCtorPoint (stagePrepared p).z) = .ok (.Ok w) ∧
          self = AspisR1S9FinishActualConstructorSlotV1.fromCtorWeights w ∧
          AspisR1S9FactorTableSemanticsV1.Meaning w.factors model ∧
          AspisR1S9StatementFactorOuterSemanticsV1.RowsPrefix w.points model 3 ∧
          AspisR1S9ConstructorV3CompleteFactorSemanticsV1.CircleRows
            (AspisR1S9FinishActualConstructorSlotV1.mapArray
              AspisR1S9FinishActualConstructorSlotV1.toCtorPoint (stagePrepared p).z) model ∧
          AspisR1S9TensorIndexedMeaningV1.MeaningOn nativeDecode
            (highProduct (model k.val)) (fun i => i < 64) out := by
  obtain ⟨self, selected, nativeOut, a0, a1, ap0, ap1, libra, hnew, hrest⟩ :=
    AspisR1S9CurrentReaderNativeProducersV1.current_resume_finish_same_canonical_receiver_exact_powers_helper
      readerOps digest bytes proof publicInput hash p acc ops v a obs hresume hfinish
  obtain ⟨halpha, hz⟩ :=
    AspisR1S9CurrentReaderConstructorInputsV1.current_resume_constructor_inputs_canonical
      readerOps digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash p acc hresume
  refine ⟨self, hnew, ?_⟩
  intro k input out hk htensor
  exact actual_constructor_native_tensor_success_complete
    (stagePrepared p).variant (stagePrepared p).semantic_alpha (stagePrepared p).z
    self k input out halpha hz hk hnew htensor

#print axioms current_resume_finish_same_constructor_tensor_semantics
end AspisR1S9CurrentResumeFinishNativeTensorV1
