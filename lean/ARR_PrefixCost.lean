import RPx_AttemptPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_PrefixCost
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Precise cost loss for partial syscalls: ideal issued addresses contain
ALL original native attempts, including the failed call, plus a suffix.
No equality of the original and extended work metrics is inferred. -/
theorem suffix {A : Type} (code : Code A)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    ∃ remaining : List Bytes,
      (eval H (SdkC_Oracle.program code)).1.map Prod.fst =
        RPx_AttemptPrefix.addresses (SdkC_Source.run hashv code []).2 ++ remaining ∧
      (eval H (SdkC_Oracle.program code)).1.length =
        (SdkC_Source.run hashv code []).2.length + remaining.length := by
  obtain ⟨kept,remaining,native,ideal⟩ := RPx_AttemptPrefix.transport code hashv sha256 H p1 syscall []
  have same : RPx_AttemptPrefix.addresses (SdkC_Source.run hashv code []).2 = kept := by
    simpa only [RPx_AttemptPrefix.addresses,List.map_nil,List.nil_append] using native
  refine ⟨remaining,?_,?_⟩
  · rw [same]
    exact ideal
  · have lengths := congrArg List.length ideal
    rw [List.length_map,List.length_append,← same] at lengths
    simpa only [RPx_AttemptPrefix.addresses,List.length_map] using lengths

theorem native_le_ideal {A : Type} (code : Code A)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    (SdkC_Source.run hashv code []).2.length ≤ (eval H (SdkC_Oracle.program code)).1.length := by
  obtain ⟨remaining,_,count⟩ := suffix code hashv sha256 H p1 syscall
  rw [count]
  exact Nat.le_add_right _ _

theorem same_cost_iff_empty {A : Type} (code : Code A)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (remaining : List Bytes)
    (count : (eval H (SdkC_Oracle.program code)).1.length =
      (SdkC_Source.run hashv code []).2.length + remaining.length) :
    (eval H (SdkC_Oracle.program code)).1.length = (SdkC_Source.run hashv code []).2.length ↔
      remaining = [] := by
  rw [count]
  constructor
  · intro same
    exact List.length_eq_zero_iff.mp (by omega)
  · rintro rfl
    exact Nat.add_zero _

#print axioms suffix
#print axioms native_le_ideal
#print axioms same_cost_iff_empty
end AspisR1.ARR_PrefixCost
end
