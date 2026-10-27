import RPt_BEi_RecorderCut
import RPt_BEf_Batches
import RPz7_GExq_BatchBudget
import RPz8_GExp_PartialCount
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_BatchCut
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Source-local TX1 batch cut. The step relation is explicit; this theorem
does not assert it follows from the erased native return. -/
theorem current {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize)
    (state after : S) (before log : Log)
    (value : Result (core.result.Result Unit AspisR1CurrentCaller.verifier.Error))
    (execution : Executes call (SdkC_BatchSource.currentCode hashv proof p root)
      state before value after log) :
    value = Op5T_Install.currentBatch Port4B_Install.leaves D proof p root 0#usize () ∧
    BEh_Scope.Law (value,after,log)
      (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv proof p root) state before) ∧
    log = before ++ BEi_RecorderCut.issued before log ∧
    BEi_RecorderCut.issued before log =
      (SdkC_Source.run hashv (SdkC_BatchSource.currentCode hashv proof p root) []).2 := by
  have cut := BEi_CutProjection.source call hashv binding _ state after before log value execution
  have values := congrArg Prod.fst cut
  change value = _ at values
  exact ⟨values.trans (SdkC_BatchSource.current_source hashv D source proof p root before),
    BEi_CutProjection.observation call _ state after before log value execution,
    (BEi_RecorderCut.exact_cut call _ state after before log value execution).1,
    BEi_RecorderCut.source_cut call hashv binding _ state after before log value execution⟩

/-- Source-local TX2 uses the actual resumed Prepared/query/root carrier. -/
theorem stage {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize)
    (state after : S) (before log : Log)
    (value : Result (core.result.Result Unit VTop_Stages.verifier.Error))
    (execution : Executes call (SdkC_BatchSource.stageCode hashv proof p root)
      state before value after log) :
    value = Op5T_Install.stageBatch Port4B_Install.leaves D proof p root 1#usize () ∧
    BEh_Scope.Law (value,after,log)
      (BEf_Carrier.run call (SdkC_BatchSource.stageCode hashv proof p root) state before) ∧
    log = before ++ BEi_RecorderCut.issued before log ∧
    BEi_RecorderCut.issued before log =
      (SdkC_Source.run hashv (SdkC_BatchSource.stageCode hashv proof p root) []).2 := by
  have cut := BEi_CutProjection.source call hashv binding _ state after before log value execution
  have values := congrArg Prod.fst cut
  change value = _ at values
  exact ⟨values.trans (SdkC_BatchSource.stage_source hashv D source proof p root before),
    BEi_CutProjection.observation call _ state after before log value execution,
    (BEi_RecorderCut.exact_cut call _ state after before log value execution).1,
    BEi_RecorderCut.source_cut call hashv binding _ state after before log value execution⟩

#print axioms current
#print axioms stage
end AspisR1.BEi_BatchCut
end
