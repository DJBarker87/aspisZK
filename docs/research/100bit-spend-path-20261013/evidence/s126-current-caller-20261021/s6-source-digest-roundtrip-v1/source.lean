import S6SourceDigestDecodeTotalV1
import S6SourceDigestEncodeContentsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.DigestRoundtrip
open AspisS6FiveUnrolledCodec

@[step] theorem option_binding_spec {T E : Type} (value : Option T) (error : E) :
    AspisS6StdOptionMethods.option_ok_or value error
      ⦃ result => ∀ x, result=core.result.Result.Ok x → value=some x ⦄ := by
  apply exists_imp_spec
  cases value <;> refine ⟨_,rfl,?_⟩ <;> simp

theorem bytes_expansion (bytes : Array U8 32#usize) :
    [bytes.val[0]'(by rw [bytes.property]; decide),
     bytes.val[1]'(by rw [bytes.property]; decide),
     bytes.val[2]'(by rw [bytes.property]; decide),
     bytes.val[3]'(by rw [bytes.property]; decide),
     bytes.val[4]'(by rw [bytes.property]; decide),
     bytes.val[5]'(by rw [bytes.property]; decide),
     bytes.val[6]'(by rw [bytes.property]; decide),
     bytes.val[7]'(by rw [bytes.property]; decide),
     bytes.val[8]'(by rw [bytes.property]; decide),
     bytes.val[9]'(by rw [bytes.property]; decide),
     bytes.val[10]'(by rw [bytes.property]; decide),
     bytes.val[11]'(by rw [bytes.property]; decide),
     bytes.val[12]'(by rw [bytes.property]; decide),
     bytes.val[13]'(by rw [bytes.property]; decide),
     bytes.val[14]'(by rw [bytes.property]; decide),
     bytes.val[15]'(by rw [bytes.property]; decide),
     bytes.val[16]'(by rw [bytes.property]; decide),
     bytes.val[17]'(by rw [bytes.property]; decide),
     bytes.val[18]'(by rw [bytes.property]; decide),
     bytes.val[19]'(by rw [bytes.property]; decide),
     bytes.val[20]'(by rw [bytes.property]; decide),
     bytes.val[21]'(by rw [bytes.property]; decide),
     bytes.val[22]'(by rw [bytes.property]; decide),
     bytes.val[23]'(by rw [bytes.property]; decide),
     bytes.val[24]'(by rw [bytes.property]; decide),
     bytes.val[25]'(by rw [bytes.property]; decide),
     bytes.val[26]'(by rw [bytes.property]; decide),
     bytes.val[27]'(by rw [bytes.property]; decide),
     bytes.val[28]'(by rw [bytes.property]; decide),
     bytes.val[29]'(by rw [bytes.property]; decide),
     bytes.val[30]'(by rw [bytes.property]; decide),
     bytes.val[31]'(by rw [bytes.property]; decide)]=bytes.val := by
  apply List.ext_getElem
  · simp [bytes.property]
  · intro i hi hj
    have hi32 : i<32 := by simpa using hi
    interval_cases i <;> rfl

@[step] theorem decoded_contents (bytes : Array U8 32#usize) :
    aspis_statement.atomic_statement.decode_digest_canonical bytes
      ⦃ result => ∀ digest, result=core.result.Result.Ok digest →
        DigestContents.chunks digest=bytes.val ⦄ := by
  unfold aspis_statement.atomic_statement.decode_digest_canonical
  step*
  all_goals (intro digest hd; cases hd)
  all_goals (simp_all only [DigestContents.chunks,
    aspis_core.field.M31.to_le_bytes,Result.ok.injEq,Array.make])

#print axioms bytes_expansion
#print axioms decoded_contents
end AspisS6SourceCodec.DigestRoundtrip
