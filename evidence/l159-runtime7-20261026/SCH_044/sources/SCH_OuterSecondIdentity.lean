import SCH_SdkSecond
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_OuterSecondIdentity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem code {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (id : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    S2W_Outer.stage2_owned
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) S2W_Outer.traceEffects id accounts data slot =
    S2W_Outer.stage2_owned (SCH_IdealSdk.dictionary c hashv H)
      S2W_Outer.traceEffects id accounts data slot := by
  simp only [S2W_Outer.stage2_owned,SCH_SdkSecond.validation,SCH_SdkSecond.range,
    SCH_SdkSecond.option_eq,SCH_SdkSecond.statement_bytes,SCH_SdkPure.data,
    SCH_SdkPure.prefix_bytes,SCH_SdkPure.digest,SCH_SdkPure.observer]

#print axioms code
end AspisR1.SCH_OuterSecondIdentity
end
