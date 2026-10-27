import RPz7_S1SemanticCodeFinishV1
import RPz7_S1SemanticCodeRoundsExactV1
import RPz7_S1SemanticCodeCircleValidatedExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Complete original source outcome, including early rejection and outer failure. -/
theorem finish_erasure (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)
    (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    erase (finish R B D pub prefix1 transcript challenges obs)=FinishModel.finish R B D pub prefix1 transcript challenges obs := by
  unfold finish FinishModel.finish
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | apply rounds_erasure)
    | (solve | apply circleValidated_erasure)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [rounds_erasure] | rw [circleValidated_erasure]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

#print axioms finish_erasure
end AspisR1PublicPreparation.S1SemanticCode
