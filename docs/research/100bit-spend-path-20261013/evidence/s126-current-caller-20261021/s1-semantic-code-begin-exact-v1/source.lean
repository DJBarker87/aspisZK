import S1SemanticCodeBeginV1
import S1SemanticCodeSemanticValidatedExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

theorem begin13_erasure_native {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript13 : r1_wire.SemanticTranscript H)
    (val val1 val2 val12 : aspis_core.field.QM31)
    (index_mut_back9 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    erase (begin13 D prefix1 transcript13 val val1 val2 val12 index_mut_back9)=begin13_native D prefix1 transcript13 val val1 val2 val12 index_mut_back9 := by
  unfold begin13 begin13_native
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [semanticValidated_erasure]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

theorem begin9_erasure_native {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript9 : r1_wire.SemanticTranscript H)
    (val val1 val2 val8 : aspis_core.field.QM31)
    (index_mut_back5 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    erase (begin9 D prefix1 transcript9 val val1 val2 val8 index_mut_back5)=begin9_native D prefix1 transcript9 val val1 val2 val8 index_mut_back5 := by
  unfold begin9 begin9_native
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [semanticValidated_erasure] | rw [begin13_erasure_native]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

theorem begin5_erasure_native {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript5 : r1_wire.SemanticTranscript H)
    (val val1 val2 val4 : aspis_core.field.QM31)
    (index_mut_back1 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    erase (begin5 D prefix1 transcript5 val val1 val2 val4 index_mut_back1)=begin5_native D prefix1 transcript5 val val1 val2 val4 index_mut_back1 := by
  unfold begin5 begin5_native
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [semanticValidated_erasure] | rw [begin9_erasure_native]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

theorem begin_erasure_native {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    erase (begin D prefix1 transcript)=begin_native D prefix1 transcript := by
  unfold begin begin_native
  repeat' first
    | (solve | exact erase_lift _)
    | (solve | exact erase_pure _)
    | (solve | rfl)
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [semanticValidated_erasure] | rw [begin5_erasure_native]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

/-- Fission is definitionally the same retained source body. All captures,
rejections and current transcript values are retained without a success premise. -/
theorem begin_native_eq {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    begin_native D prefix1 transcript=r1_wire.begin D prefix1 transcript := by
  unfold begin_native begin5_native begin9_native begin13_native r1_wire.begin
  rfl

theorem begin_erasure {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    erase (begin D prefix1 transcript)=r1_wire.begin D prefix1 transcript := by
  rw [begin_erasure_native,begin_native_eq]

#print axioms begin_native_eq
#print axioms begin_erasure
end AspisR1PublicPreparation.S1SemanticCode
