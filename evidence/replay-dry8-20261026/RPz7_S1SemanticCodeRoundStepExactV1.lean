import RPz7_S1SemanticCodeRoundStepV1
import RPz7_S1SemanticCodeSemanticValidatedExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Complete original source outcome, including early rejection and outer failure. -/
theorem roundStep_erasure (B : RoundModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
    (alpha : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Usize) :
    erase (roundStep B D prefix1 transcript alpha running round)=RoundModel.step B D prefix1 transcript alpha running round := by
  unfold roundStep RoundModel.step
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | apply semanticValidated_erasure)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [semanticValidated_erasure]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

#print axioms roundStep_erasure
end AspisR1PublicPreparation.S1SemanticCode
