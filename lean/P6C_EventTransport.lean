import P6C_Irrelevance
import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_EventTransport
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- A security event on the full ordered oracle history and accepted value.
The carrier, query order and repetitions are shared with the ideal event. -/
def realEvent {A : Type} (hashv : Parts → Result Digest) (code : Code A)
    (bad : List (Bytes × State) → A → Prop) : Prop :=
  ∃ value, (run hashv code []).1 = ok value ∧ bad (readLog (run hashv code []).2) value

def idealEvent {A : Type} (H : Bytes → State) (code : Code A)
    (bad : List (Bytes × State) → A → Prop) : Prop :=
  ∃ value, (eval H (SdkC_Oracle.program code)).2 = ok value ∧
    bad (eval H (SdkC_Oracle.program code)).1 value

/-- Exact accepted-result/log transport implies event inclusion, with NO
conditioning factor and no converse assertion for unaccepted real runs. -/
theorem inclusion {A : Type} (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (code : Code A) (bad : List (Bytes × State) → A → Prop) :
    realEvent hashv code bad → idealEvent H code bad := by
  rintro ⟨value,accepted,failure⟩
  have exactRun := SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall code value accepted
  exact ⟨value,by rw [exactRun],by simpa only [exactRun] using failure⟩

/-- Finite weighted laws are bounded by the SAME unconditioned ideal-event
mass. No division by real acceptance probability is introduced. The generic
weights need only be nonnegative; normalization can be supplied by a caller. -/
theorem mass {I A : Type} (worlds : Finset I) (weight : I → Rat)
    (nonnegative : ∀ i ∈ worlds, 0 ≤ weight i)
    (hashv : I → Parts → Result Digest) (sha256 H : I → Bytes → State)
    (p1 : ∀ i, S2W_ExtractionBoundary.P1 (sha256 i) (H i))
    (syscall : ∀ i, S2W_ExtractionBoundary.RuntimeSyscall (hashv i) (sha256 i))
    (code : I → Code A) (bad : List (Bytes × State) → A → Prop) :
    (∑ i ∈ worlds, if realEvent (hashv i) (code i) bad then weight i else 0) ≤
      ∑ i ∈ worlds, if idealEvent (H i) (code i) bad then weight i else 0 := by
  classical
  apply Finset.sum_le_sum
  intro i member
  by_cases occurs : realEvent (hashv i) (code i) bad
  · have ideal := inclusion (hashv i) (sha256 i) (H i) (p1 i) (syscall i) (code i) bad occurs
    simp only [if_pos occurs,if_pos ideal,le_refl]
  · simp only [if_neg occurs]
    split
    · exact nonnegative i member
    · exact le_refl _

#print axioms inclusion
#print axioms mass
end AspisR1.P6C_EventTransport
end
