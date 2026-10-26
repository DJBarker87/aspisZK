import SCE_FailureZero
import SCE_AccountMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_RejectedAccount
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A)

/-- Rejection contributes zero extraction failure while preserving all
issued queries in the experiment, including a failing verifier prefix. -/
theorem zero (H : Bytes → State)
    (rejected : accepted (eval H (account c hashv copy allocator id a)).2 ≠ true) :
    F3T_Runtime.runtimeMass (eval H (runtime c hashv copy allocator id a)) = 0 := by
  rw [SCE_AccountMass.pointwise]
  apply SCE_FailureZero.rejected
  exact rejected

#print axioms zero
end AspisR1.SCE_RejectedAccount
end
