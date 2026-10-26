import ExtractedRecordByteValue
set_option autoImplicit false
namespace AspisR1.JFw_HeaderCast
open Aeneas Aeneas.Std Result

theorem eq (a b c d : U8) (size : Usize)
    (value : a.val+256*b.val+65536*c.val+16777216*d.val = size.val) :
    UScalar.cast .Usize (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])) = size := by
  let word := core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])
  have decoded : word.val = size.val := (ExtractedRecordByteValue.from_le4_value a b c d).trans value
  have bound : word.val ≤ UScalar.max .Usize := by rw [decoded];scalar_tac
  have cast := UScalar.cast_inBounds_spec .Usize word bound
  change (UScalar.cast .Usize word).val = word.val at cast
  exact UScalar.eq_of_val_eq (cast.trans decoded)

#print axioms eq
end AspisR1.JFw_HeaderCast
