import S1SemanticCodeSampleBlockV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Exact source call on ALL outcomes. Row-order failure, checked arithmetic,
ordered absorb/squeeze/advance digest calls and the returned row/state remain. -/
theorem sampleBlock_erasure {H : Type} (D : aspis_core.Digest32 H)
    (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    erase (sampleBlock D self row framed)=
      r1_wire.SemanticTranscript.sample_block_validated D self row framed := by
  unfold sampleBlock r1_wire.SemanticTranscript.sample_block_validated
  split
  · rfl
  · repeat' first
      | (rw [erase_bind]
         first | rw [erase_lift] | rw [erase_digest]
         apply bind_congr
         intro x)
      | (apply bind_congr;intro x)
      | (exact erase_pure _)
      | rfl

#print axioms sampleBlock_erasure
end AspisR1PublicPreparation.S1SemanticCode
