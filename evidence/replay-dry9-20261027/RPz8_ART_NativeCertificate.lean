import RPz8_ART_NativeAgreement
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_NativeCertificate
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment ARS_NativeAccount

theorem original {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native : Bytes → State) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native) :
    ART_PartialAccount.Certificate c hashv copy allocator id a native native := by
  refine ⟨?_,ART_NativeAgreement.issued hashv native syscall _,?_⟩
  · intro bytes member; rfl
  · intro saved post final first
    exact ⟨(by intro bytes member; rfl),ART_NativeAgreement.issued hashv native syscall _⟩

#print axioms original
end AspisR1.ART_NativeCertificate
end
