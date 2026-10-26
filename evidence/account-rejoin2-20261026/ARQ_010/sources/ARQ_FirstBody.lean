import ARQ_LowerTrace
import SCH_SourceFirst
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_FirstBody
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Execution GExq_AccountExperiment

/-- A successful actual first wrapper constructs its own world-indexed outer
trace. Allocation/copy/cleanup add no oracle reads. No native run is inverted. -/
theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (i : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (final : A) (H : Bytes → State)
    (success : (eval H (firstCode c hashv copy allocator id i)).2 = ok (.Ok (saved,post,final))) :
    ∃ log,
      S2W_Trace.run (SCH_IdealSdk.dictionary c hashv H)
        (S2W_Outer.stage1_owned (SCH_IdealSdk.dictionary c hashv H)
          S2W_Outer.traceEffects id i.entry.first i.data) [] = ok (.Ok saved,log) ∧
      (eval H (firstCode c hashv copy allocator id i)).1 = ARQ_LowerTrace.trace c hashv H log := by
  obtain ⟨allocated,reserved,body⟩ := SCH_WrapperFirst.body _ copy allocator i.entry i.state final saved post H success
  have original := SCH_Lower.result c hashv H
    (S2W_Outer.stage1_owned (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std) S2W_Outer.traceEffects id i.entry.first i.data)
  rw [SCH_OuterFirstIdentity.code c hashv H id i.entry.first i.data] at original
  have result : S2W_Trace.erase (SCH_IdealSdk.dictionary c hashv H)
      (S2W_Outer.stage1_owned (SCH_IdealSdk.dictionary c hashv H)
        S2W_Outer.traceEffects id i.entry.first i.data) = ok (.Ok saved) := by
    unfold GExq_Caller.first at body
    rw [SCH_OuterFirstIdentity.code c hashv H id i.entry.first i.data] at body
    exact original.symm.trans body
  obtain ⟨log,ran⟩ := S2W_TraceFacts.success_exists _ _ [] _ result
  refine ⟨log,ran,?_⟩
  have flattened := ARQ_LowerTrace.flatten c hashv H _ [] log (core.result.Result.Ok saved) ran
  have wrapper := SCG_WrapperLog.first _ hashv copy allocator i.entry i.state allocated reserved H
  change (eval H (firstCode c hashv copy allocator id i)).1 =
    (eval H (SdkC_Oracle.program (GExq_Caller.first c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std hashv id i.entry.first i.data))).1 at wrapper
  rw [wrapper]
  unfold GExq_Caller.first
  rw [SCH_OuterFirstIdentity.code c hashv H id i.entry.first i.data]
  exact flattened

#print axioms accepted
end AspisR1.ARQ_FirstBody
end
