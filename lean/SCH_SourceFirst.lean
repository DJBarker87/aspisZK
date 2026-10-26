import SCH_Lower
import SCH_WrapperFirst
import SCH_OuterFirstIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_SourceFirst
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Execution GExq_AccountExperiment

theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (i : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (final : A) (H : Bytes → State)
    (success : (eval H (firstCode c hashv copy allocator id i)).2 = ok (.Ok (saved,post,final))) :
    AdapterRw.r1_pool_adapter.owned.stage1_owned (SCH_IdealSdk.dictionary c hashv H)
      id i.entry.first i.data = ok (.Ok saved) := by
  obtain ⟨allocated,reserved,body⟩ := SCH_WrapperFirst.body _ copy allocator i.entry i.state final saved post H success
  have same := SCH_Lower.result c hashv H
    (S2W_Outer.stage1_owned (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std) S2W_Outer.traceEffects id i.entry.first i.data)
  rw [SCH_OuterFirstIdentity.code c hashv H id i.entry.first i.data,
    S2W_OuterErasure.stage1_erasure] at same
  unfold GExq_Caller.first at body
  rw [SCH_OuterFirstIdentity.code c hashv H id i.entry.first i.data] at body
  exact same.symm.trans body

#print axioms accepted
end AspisR1.SCH_SourceFirst
end
