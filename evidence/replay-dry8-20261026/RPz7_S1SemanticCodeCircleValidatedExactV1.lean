import RPz7_S1SemanticCodeCircleValidatedV1
import RPz7_S1SemanticCodeSampleBlockExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Complete original source outcome, including early rejection and outer failure. -/
theorem circleValidated_erasure (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
    erase (circleValidated B D self record1)=FinishModel.circle_validated B D self record1 := by
  unfold circleValidated FinishModel.circle_validated
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | simp_all)
    | (solve | apply sampleBlock_erasure)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [sampleBlock_erasure]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

#print axioms circleValidated_erasure
end AspisR1PublicPreparation.S1SemanticCode
