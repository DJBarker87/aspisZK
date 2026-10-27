import RPz8_ART_NativeCertificate
import RPz8_ART_OriginalLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_NativeCoverage
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment ARS_NativeAccount

/-- For EVERY original adversary, the fixed-native experiment has the exact
partial source outcome and original attempted cost. No syscall-success premise,
accepted-wrapper premise or bank-support promise is used for representation. -/
theorem original {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native : Bytes → State) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) native1 native2 hashv) :
    (eval native (ART_PartialAccount.account c hashv copy allocator id a)).2 =
      ARS_NativeOutcome.wrappers copy allocator id a native1 native2 native ∧
    (eval native (ART_PartialAccount.account c hashv copy allocator id a)).1.length =
      attempts c hashv copy allocator id a native := by
  have cert := ART_NativeCertificate.original c hashv copy allocator id a native syscall
  exact ⟨ART_Outcome.native c hashv copy allocator id a native native cert native1 native2 extraction,
    ART_Cost.exact c hashv copy allocator id a native native cert⟩

#print axioms original
end AspisR1.ART_NativeCoverage
end
