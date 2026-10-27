import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_WorldCompatibility
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

def Compatible (H : AspisV8R19.DuplexFrames.Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) : Prop :=
  ∀ parts digest, hashv parts = .ok digest → decodeState digest = H (flatten parts)

/-- Exact class of worlds admitted by P1 plus returning-value RuntimeSyscall,
with hashv FIXED before the world quantifier. No native acceptance is assumed. -/
theorem iff_witness (H : AspisV8R19.DuplexFrames.Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    Compatible H hashv ↔ ∃ sha256 : AspisV8R19.DuplexFrames.Bytes → State,
      S2W_ExtractionBoundary.P1 sha256 H ∧
      S2W_ExtractionBoundary.RuntimeSyscall hashv sha256 := by
  constructor
  · intro compatible
    exact ⟨H,⟨fun _ => rfl⟩,⟨compatible⟩⟩
  · rintro ⟨sha,p1,syscall⟩ parts digest returned
    exact (syscall.returningValue parts digest returned).trans (p1.realization _)

theorem separates (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (H K : AspisV8R19.DuplexFrames.Bytes → State) (p : SdkC_Source.Parts) (d : SdkC_Source.Digest)
    (returned : hashv p = .ok d) (different : H (flatten p) ≠ K (flatten p)) :
    ¬ (Compatible H hashv ∧ Compatible K hashv) := by
  rintro ⟨h,k⟩
  exact different ((h p d returned).symm.trans (k p d returned))

/-- A fixed returning native hash dictionary cannot satisfy the retained
oracle interface for EVERY world. This does not refute acceptance-guarded
support; that would also require acceptance in incompatible worlds. -/
theorem not_all_worlds (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : SdkC_Source.Parts) (d : SdkC_Source.Digest) (returned : hashv p = .ok d) :
    ¬ ∀ H : AspisV8R19.DuplexFrames.Bytes → State, Compatible H hashv := by
  intro all
  let zero : Bytes → State := fun _ _ => 0
  let one : Bytes → State := fun _ _ => 1
  have different : zero (flatten p) ≠ one (flatten p) := by
    intro same
    have atZero := congrFun same 0
    exact (by decide : (0 : AspisV8R19.DuplexFrames.Byte) ≠ 1) atZero
  exact separates hashv zero one p d returned different ⟨all zero,all one⟩

#print axioms iff_witness
#print axioms separates
#print axioms not_all_worlds
end AspisR1.ARR_WorldCompatibility
end
