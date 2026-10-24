import S9Tx2CurrentKappaEndpointV1
import S9ConstructorV3CompleteFactorSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9SourceResumeConstructorModelV1
open AspisR1S9ResumeFinishNativePairBindingV1
open AspisR1S9ResumeConstructorInputsCanonicalV1
open AspisR1S9FinishActualConstructorSlotV1
open AspisR1S9FactorTableSemanticsV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
/-- The actual constructor event and SAME strict source resume choose ONE
complete table model with statement D18 and circle meanings. No independent
Current View/finish, input canonicality or per-row model is supplied. The
actual caller supplies these SAME resume/new events; this pure constructor
bridge is not a complete spend-relation or runtime theorem. -/
theorem source_resume_same_constructor_complete_model {H : Type}
    (ops : AspisR1Stage2.ResumeOps)
    (digest : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (variant : AspisR1Stage2.transport.Variant) (hash : H)
    (p : AspisR1Stage2.verifier.Prepared) (acc : AspisR1Stage2.verifier.Accumulator)
    (self : AspisR1S9ProductionPairCutV1.weights.Weights)
    (hresume : AspisR1Stage2.verifier.resumeWithOps
      (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops)
      digest bytes proof publicInput variant hash=.ok (.Ok (p,acc)))
    (hnew : actualNewWeightsSlot (stagePrepared p).variant (stagePrepared p).semantic_alpha
      (stagePrepared p).z=.ok (.Ok self)) :
    ∃ (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights) (model : Table),
      AspisR1S9ActualWeightsNewBoxNewV3.weights_new (toCtorVariant (stagePrepared p).variant)
        (inputAlpha p) (inputZ p)=.ok (.Ok w) ∧
      self=fromCtorWeights w ∧ Meaning w.factors model ∧
      AspisR1S9StatementFactorOuterSemanticsV1.RowsPrefix w.points model 3 ∧
      AspisR1S9ConstructorV3CompleteFactorSemanticsV1.CircleRows (inputZ p) model ∧
      AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.r0.statement_points (inputAlpha p)=.ok w.points ∧
      w.variant=toCtorVariant (stagePrepared p).variant ∧
      ∃ q8 q9 : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31,
        Array.index_usize (inputAlpha p) 8#usize=.ok q8 ∧
        Array.index_usize (inputAlpha p) 9#usize=.ok q9 ∧ w.extra=Array.make 2#usize [q8,q9] := by
  obtain ⟨halpha,hz⟩ :=
    AspisR1S9CurrentReaderConstructorInputsV1.current_resume_constructor_inputs_canonical
      ops digest bytes proof publicInput variant hash p acc hresume
  obtain ⟨w,hsource,hself⟩ := actualNewWeightsSlot_success
    (stagePrepared p).variant (stagePrepared p).semantic_alpha (stagePrepared p).z self hnew
  obtain ⟨model,hm,hrows,hcircle,hpoints,hvariant,hextra⟩ :=
    AspisR1S9ConstructorV3CompleteFactorSemanticsV1.constructor_success_complete_factor_semantics
      (toCtorVariant (stagePrepared p).variant) (inputAlpha p) (inputZ p) w halpha hz hsource
  exact ⟨w,model,hsource,hself,hm,hrows,hcircle,hpoints,hvariant,hextra⟩
#print axioms source_resume_same_constructor_complete_model
end AspisR1S9SourceResumeConstructorModelV1
