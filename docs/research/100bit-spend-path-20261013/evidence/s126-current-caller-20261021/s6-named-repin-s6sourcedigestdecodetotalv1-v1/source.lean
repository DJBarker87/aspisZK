import S6SourceWordInverseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.DigestDecode
open AspisS6FiveUnrolledCodec

@[step] theorem word_spec (bytes : Array U8 4#usize) :
    aspis_core.field.M31.from_le_bytes bytes
      ⦃ result => ∀ value, result=some value →
        aspis_core.field.M31.to_le_bytes value=ok bytes ⦄ := by
  obtain ⟨result,hr⟩ := WordInverse.decode_total bytes
  rw [hr,WP.spec_ok]
  intro value hv
  exact WordInverse.accepted_roundtrip bytes value (hr.trans (congrArg ok hv))

@[step] theorem option_spec {T E : Type} (value : Option T) (error : E) :
    AspisS6StdOptionMethods.option_ok_or value error ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases value <;> exact ⟨_,rfl,trivial⟩

/-- TOTAL actual complete digest decoder, including noncanonical rejection. -/
@[step] theorem decode_spec (bytes : Array U8 32#usize) :
    aspis_statement.atomic_statement.decode_digest_canonical bytes ⦃ _ => True ⦄ := by
  unfold aspis_statement.atomic_statement.decode_digest_canonical
  step*

theorem decode_total (bytes : Array U8 32#usize) :
    ∃ result, aspis_statement.atomic_statement.decode_digest_canonical bytes=ok result := by
  obtain ⟨result,h,_⟩ := spec_imp_exists (decode_spec bytes)
  exact ⟨result,h⟩

#print axioms word_spec
#print axioms decode_total
end AspisS6SourceCodec.DigestDecode
