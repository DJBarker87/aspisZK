import ARW_Induced
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARW_WrapperNative
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
/-- Whole Result equality, including rejection and divergence. Agreement is
only on the actual source log, not unissued addresses. -/
theorem first {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) native1 native2 hashv)
    (i : FirstInputs A) (H : Bytes → State)
    (agrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
      (ARS_NativeAccount.firstSyntax c hashv copy allocator id i) []).2) :
    (eval H (ART_PartialAccount.wrapper hashv
      (ARS_NativeAccount.firstSyntax c hashv copy allocator id i))).2 =
      S2W_D189Wrappers.first native1 copy allocator i.entry id i.data i.state := by
  rw [ART_WrapperExact.execution hashv H _ agrees,SdkC_Source.erasure]
  exact GExq_InstalledWrapper.first_source c.adapter c.currentBase c.stageBase c.finish c.reserved
    c.query c.geometry c.boundaries c.std hashv copy allocator i.entry id i.data i.state
    native1 native2 extraction

#print axioms first
end AspisR1.ARW_WrapperNative
end
