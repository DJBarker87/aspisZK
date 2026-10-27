import RPz8_ART_NativeCoverage
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_QueriedCoverage
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment

/-- Lead's exact queried-address form, for EVERY adversary and ALL original
partial outcomes. Failed attempts belong to this queried set as well. -/
theorem original {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native H : Bytes → State) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (consistent : ARS_AccountReplay.Consistent
      (ART_PartialAccount.account c hashv copy allocator id a) native H)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) native1 native2 hashv) :
    eval H (ART_PartialAccount.account c hashv copy allocator id a) =
      eval native (ART_PartialAccount.account c hashv copy allocator id a) ∧
    (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 =
      ARS_NativeOutcome.wrappers copy allocator id a native1 native2 native ∧
    (eval H (ART_PartialAccount.account c hashv copy allocator id a)).1.length =
      ARS_NativeAccount.attempts c hashv copy allocator id a native := by
  have replay := ARS_AccountReplay.replay _ native H consistent
  refine ⟨replay,?_⟩
  rw [replay]
  exact ART_NativeCoverage.original c hashv copy allocator id a native syscall native1 native2 extraction

#print axioms original
end AspisR1.ART_QueriedCoverage
end
