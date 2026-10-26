import ART_NativeCoverage
import ART_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_RejectedNative
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment ARS_NativeAccount

theorem mass {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native H : Bytes → State)
    (certificate : ART_PartialAccount.Certificate c hashv copy allocator id a native H)
    (reject : accepted (ARS_NativeAccount.run c hashv copy allocator id a native).2 = false) :
    F3T_Runtime.runtimeMass (eval H (ART_Runtime.runtime c hashv copy allocator id a)) = 0 ∧
    (eval H (ART_PartialAccount.account c hashv copy allocator id a)).1.length =
      attempts c hashv copy allocator id a native := by
  refine ⟨ART_Runtime.rejected c hashv copy allocator id a H ?_,ART_Cost.exact c hashv copy allocator id a native H certificate⟩
  rw [ART_Outcome.exact c hashv copy allocator id a native H certificate]
  exact reject

#print axioms mass
end AspisR1.ART_RejectedNative
end
