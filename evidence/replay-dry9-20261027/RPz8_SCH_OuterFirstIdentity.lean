import RPz8_SCH_SdkPure
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_OuterFirstIdentity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem code {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (id : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) :
    S2W_Outer.stage1_owned
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) S2W_Outer.traceEffects id accounts data =
    S2W_Outer.stage1_owned (SCH_IdealSdk.dictionary c hashv H)
      S2W_Outer.traceEffects id accounts data := by
  simp only [S2W_Outer.stage1_owned,S2W_Outer.first_decoded,SCH_SdkPure.distinct,
    SCH_SdkPure.checkpoint,SCH_SdkPure.data,SCH_SdkPure.prefix_bytes,
    SCH_SdkPure.digest,SCH_SdkPure.observer]

#print axioms code
end AspisR1.SCH_OuterFirstIdentity
end
