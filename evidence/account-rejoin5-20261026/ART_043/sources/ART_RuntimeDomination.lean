import ART_RuntimeAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_RuntimeDomination
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Runtime
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

/-- All partial-syscall rejections contribute zero. The original total account
can be used as an upper bound; its potentially longer rejected suffix is NEVER
asserted to be actual deployed work. -/
theorem pointwise (H : Bytes → State) :
    runtimeMass (eval H (ART_Runtime.runtime c hashv copy allocator id a)) ≤
      runtimeMass (eval H (SCE_Experiment.runtime c hashv copy allocator id a)) := by
  by_cases ha : accepted (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 = true
  · rw [ART_RuntimeAccepted.exact c hashv copy allocator id a H ha]
  · have reject : accepted (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 = false :=
      Bool.eq_false_iff.mpr ha
    rw [ART_Runtime.rejected c hashv copy allocator id a H reject,SCE_Experiment.runtime_eval]
    exact F3T_Runtime.nonnegative _

theorem averaged : deployedFailure (ART_Runtime.runtime c hashv copy allocator id a) ≤
    deployedFailure (SCE_Experiment.runtime c hashv copy allocator id a) := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  exact pointwise c hashv copy allocator id a

#print axioms pointwise
#print axioms averaged
end AspisR1.ART_RuntimeDomination
end
