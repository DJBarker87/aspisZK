import S1SemanticCodeRoundsV1
import S1SemanticCodeRoundStepExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Complete original source outcome, including early rejection and outer failure. -/
theorem rounds_erasure (B : RoundModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    erase (rounds B D prefix1 transcript)=RoundModel.rounds B D prefix1 transcript := by
  unfold rounds RoundModel.rounds
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | apply roundStep_erasure)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [roundStep_erasure]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

#print axioms rounds_erasure
end AspisR1PublicPreparation.S1SemanticCode
