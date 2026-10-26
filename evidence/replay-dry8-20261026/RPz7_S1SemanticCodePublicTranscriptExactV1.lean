import RPz7_S1SemanticCodePublicTranscriptV1
import RPz7_S1SemanticCodeNewTranscriptExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Exact complete source return, with errors and outer fail/div retained. -/
theorem publicTranscript_erasure {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) :
    erase (publicTranscript D pub hash root)=r1_semantic.public_transcript D pub hash root := by
  unfold publicTranscript r1_semantic.public_transcript
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [erase_digest] | rw [newTranscript_erasure]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

#print axioms publicTranscript_erasure
end AspisR1PublicPreparation.S1SemanticCode
