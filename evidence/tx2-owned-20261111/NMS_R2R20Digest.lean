import NMS_R2R20Helpers
set_option autoImplicit false
namespace NMS_R2R20Digest
open Aeneas Aeneas.Std Result WP AspisR20Request
/-- Reuse the coherent word decoder totality at identical bit patterns. -/
theorem word_eq (bytes : Array U8 4#usize) :
 aspis_core.field.M31.from_le_bytes bytes =
 AspisS6SourceCodec.aspis_core.field.M31.from_le_bytes bytes := by
 unfold aspis_core.field.M31.from_le_bytes AspisS6SourceCodec.aspis_core.field.M31.from_le_bytes
   aspis_core.field.P AspisS6SourceCodec.aspis_core.field.P
 rfl
@[step] theorem word (bytes : Array U8 4#usize) :
 aspis_core.field.M31.from_le_bytes bytes ⦃ _ => True ⦄ := by
 rw [word_eq]
 obtain ⟨reply,run⟩ := AspisS6SourceCodec.WordInverse.decode_total bytes
 exact exists_imp_spec ⟨reply,run,trivial⟩
theorem option_eq {T E : Type} (value : Option T) (error : E) :
 core.option.Option.ok_or value error = AspisS6StdOptionMethods.option_ok_or value error := by
 cases value <;> rfl
@[step] theorem option {T E : Type} (value : Option T) (error : E) :
 core.option.Option.ok_or value error ⦃ _ => True ⦄ := by
 rw [option_eq]
 exact AspisS6SourceCodec.DigestDecode.option_spec value error
/-- Every rejecting digest is retained as an Err; outer fail/div is excluded. -/
@[step] theorem digest (bytes : Array U8 32#usize) :
 atomic_statement.decode_digest_canonical bytes ⦃ _ => True ⦄ := by
 unfold atomic_statement.decode_digest_canonical
 step*
#print axioms word_eq
#print axioms word
#print axioms option_eq
#print axioms option
#print axioms digest
end NMS_R2R20Digest
