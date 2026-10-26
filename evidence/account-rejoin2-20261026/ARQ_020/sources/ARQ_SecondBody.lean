import ARQ_LowerTrace
import SCH_SourceSecond
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_SecondBody
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Execution GExq_AccountExperiment

/-- A successful actual second wrapper constructs its own world-indexed outer
trace. Allocation/copy/cleanup add no oracle reads. No native run is inverted. -/
theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (i : SecondInputs A) (post : Heap (Nat → Record))
    (final : A) (H : Bytes → State)
    (success : (eval H (secondCode c hashv allocator id i)).2 = ok (.Ok (post,final))) :
    ∃ log,
      S2W_Trace.run (SCH_IdealSdk.dictionary c hashv H)
        (S2W_Outer.stage2_owned (SCH_IdealSdk.dictionary c hashv H)
          S2W_Outer.traceEffects id (i.entry.second secondSizes) i.data i.slot) [] = ok (.Ok (),log) ∧
      (eval H (secondCode c hashv allocator id i)).1 = ARQ_LowerTrace.trace c hashv H log := by
  obtain ⟨allocated,reserved,body⟩ := SCH_WrapperSecond.body _ allocator i.entry i.state final post H success
  have original := SCH_Lower.result c hashv H
    (S2W_Outer.stage2_owned (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std) S2W_Outer.traceEffects id (i.entry.second secondSizes) i.data i.slot)
  rw [SCH_OuterSecondIdentity.code c hashv H id (i.entry.second secondSizes) i.data i.slot] at original
  have result : S2W_Trace.erase (SCH_IdealSdk.dictionary c hashv H)
      (S2W_Outer.stage2_owned (SCH_IdealSdk.dictionary c hashv H)
        S2W_Outer.traceEffects id (i.entry.second secondSizes) i.data i.slot) = ok (.Ok ()) := by
    unfold GExq_Caller.second at body
    rw [SCH_OuterSecondIdentity.code c hashv H id (i.entry.second secondSizes) i.data i.slot] at body
    exact original.symm.trans body
  obtain ⟨log,ran⟩ := S2W_TraceFacts.success_exists _ _ [] _ result
  refine ⟨log,ran,?_⟩
  have flattened := ARQ_LowerTrace.flatten c hashv H _ [] log (core.result.Result.Ok ()) ran
  have wrapper := SCG_WrapperLog.second (GExq_Caller.second c.adapter c.currentBase c.stageBase c.finish
    c.reserved c.query c.geometry c.boundaries c.std hashv id (i.entry.second secondSizes) i.data i.slot) allocator i.entry i.state allocated reserved H
  change (eval H (secondCode c hashv allocator id i)).1 =
    (eval H (SdkC_Oracle.program (GExq_Caller.second c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std hashv id (i.entry.second secondSizes) i.data i.slot))).1 at wrapper
  rw [wrapper]
  unfold GExq_Caller.second
  rw [SCH_OuterSecondIdentity.code c hashv H id (i.entry.second secondSizes) i.data i.slot]
  exact flattened

#print axioms accepted
end AspisR1.ARQ_SecondBody
end
