import S1SemanticCodeSemanticValidatedV1
import S1SemanticCodeSampleBlockExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Exact complete source return, with errors and outer fail/div retained. -/
theorem semanticValidated_erasure {H : Type} (D : aspis_core.Digest32 H)
    (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
    erase (semanticValidated D self record1)=r1_wire.SemanticTranscript.semantic_validated D self record1 := by
  unfold semanticValidated r1_wire.SemanticTranscript.semantic_validated
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [erase_digest] | rw [sampleBlock_erasure]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

#print axioms semanticValidated_erasure
end AspisR1PublicPreparation.S1SemanticCode
