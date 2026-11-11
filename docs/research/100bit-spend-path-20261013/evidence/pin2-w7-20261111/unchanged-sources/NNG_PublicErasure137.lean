import LIB_VPublicTranscript
set_option autoImplicit false
namespace AspisR1.NNG_PublicErasure137
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.S1SemanticCode
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
end AspisR1.NNG_PublicErasure137
