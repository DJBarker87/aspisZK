import NDO_JFs_SerializerCanonical
import JFs_SerializerLengths
set_option autoImplicit false
namespace AspisR1.JFs_SerializerSize
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Frontier431
open AspisR1PublicSerializer.Whole431

theorem digest_length (a : Array U32 8#usize) : a.val.length=8 := a.property

theorem index_length (n : U64) : (core.num.U64.to_le_bytes n).val.length=8 := (core.num.U64.to_le_bytes n).property

/- PIN2 W6: the PIN2 transfer image is 1520 bytes (was 1455): W3b's `steps_bytes` and
   `PIN2_SerializerLengths.length` (1455 frozen prefix + pool 32 + domain 32 + flag 1). -/
theorem source : ((AspisR1.PIN2_PublicBytesRefinement.steps JFs_SerializerCanonical.value).flatMap
    AspisR1.PIN2_PublicBytesRefinement.stepBytes).length=1520 := by
  rw [AspisR1.PIN2_PublicBytesRefinement.steps_bytes,AspisR1.PIN2_SerializerLengths.length]
  rfl

#print axioms digest_length
#print axioms index_length
#print axioms source
end AspisR1.JFs_SerializerSize
