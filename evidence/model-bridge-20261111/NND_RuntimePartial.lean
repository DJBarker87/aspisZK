import NND_064ParseTransport
import RSL_Pool
set_option autoImplicit false
noncomputable section
namespace NND_RuntimePartial
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def stopped : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest := fun _ => .div

/-- The retained runtime item constrains successful replies only. It admits
a partial backend, as the existing source-boundary comment explicitly says. -/
theorem admitted (sha256 : Bytes → State) :
 S2W_ExtractionBoundary.RuntimeSyscall stopped sha256 := by
 constructor
 intro parts digest h
 cases h

theorem no_return (parts : S2Z.Oracle.Parts) :
 ¬ ∃ d, stopped parts = ok d := by
 rintro ⟨d,h⟩
 cases h

theorem digest_stopped (parts : S2Z.Oracle.Parts) :
 S2W_DigestExtraction.digest stopped () parts = .div := rfl

/-- Thus runtime returning-value realization alone cannot construct an EnvRep
requiring total matching hash replies. No new totality trust is introduced. -/
theorem does_not_imply_total (sha256 : Bytes → State) (parts : S2Z.Oracle.Parts) :
 ¬ (∀ hashv, S2W_ExtractionBoundary.RuntimeSyscall hashv sha256 → ∃ d, hashv parts = ok d) := by
 intro total
 exact no_return parts (total stopped (admitted sha256))

#print axioms admitted
#print axioms no_return
#print axioms digest_stopped
#print axioms does_not_imply_total
end NND_RuntimePartial
