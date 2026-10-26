import RPz7_S1SemanticCodeVerifyV1
import RPz7_S1SemanticCodeFinishExactV1
import RPz7_S1SemanticCodeBeginExactV1
import RPz7_S1SemanticCodePublicTranscriptExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Complete semantic source body, not a supplied success/trace hypothesis.
The concrete prefix, public transcript, fifteen begin rows, ten rounds and
finish all share this same call, including their actual rejection suffixes. -/
theorem verify_erasure (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    erase (verify (finish R B) D pub bytes hash obs)=
      VerifyPrefix.verify (FinishModel.finish R B) D pub bytes hash obs := by
  unfold verify VerifyPrefix.verify
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | apply finish_erasure)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [publicTranscript_erasure] | rw [begin_erasure]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

#print axioms verify_erasure
end AspisR1PublicPreparation.S1SemanticCode
