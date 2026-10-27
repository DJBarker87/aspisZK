import RPz7_S1SemanticCodeNewTranscriptV1
import RPz7_S1SemanticCodeSampleBlockExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Exact complete source return, with errors and outer fail/div retained. -/
theorem newTranscript_erasure {H : Type} (D : aspis_core.Digest32 H)
    (hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize) :
    erase (newTranscript D hash publicBytes root)=r1_wire.SemanticTranscript.new D hash publicBytes root := by
  unfold newTranscript r1_wire.SemanticTranscript.new
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [erase_digest]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

#print axioms newTranscript_erasure
end AspisR1PublicPreparation.S1SemanticCode
