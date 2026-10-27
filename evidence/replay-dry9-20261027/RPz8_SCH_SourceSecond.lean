import RPz8_SCH_Lower
import RPz8_SCH_WrapperSecond
import RPz8_SCH_OuterSecondIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_SourceSecond
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Execution GExq_AccountExperiment

theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (i : SecondInputs A) (post : Heap (Nat → Record)) (final : A) (H : Bytes → State)
    (success : (eval H (secondCode c hashv allocator id i)).2 = ok (.Ok (post,final))) :
    AdapterRw.r1_pool_adapter.owned.stage2_owned (SCH_IdealSdk.dictionary c hashv H)
      id (i.entry.second secondSizes) i.data i.slot = ok (.Ok ()) := by
  obtain ⟨allocated,reserved,body⟩ := SCH_WrapperSecond.body _ allocator i.entry i.state final post H success
  have same := SCH_Lower.result c hashv H
    (S2W_Outer.stage2_owned (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std) S2W_Outer.traceEffects id (i.entry.second secondSizes) i.data i.slot)
  rw [SCH_OuterSecondIdentity.code c hashv H id (i.entry.second secondSizes) i.data i.slot,
    S2W_OuterErasure.stage2_erasure] at same
  unfold GExq_Caller.second at body
  rw [SCH_OuterSecondIdentity.code c hashv H id (i.entry.second secondSizes) i.data i.slot] at body
  exact same.symm.trans body

#print axioms accepted
end AspisR1.SCH_SourceSecond
end
