import PV_B3P_ByteLayout226V3
namespace PV_B3P_ByteEndian226V3
open Aeneas Aeneas.Std PV_B3P_ByteLayout226V3
set_option autoImplicit false

-- Four/eight fixed byte lanes, with a symbolic input word. These do not
-- normalize a serializer recurrence or any concrete field multiplication.
set_option backward.isDefEq.respectTransparency false in
theorem word_bytes (v : U32) : wordBytes v = (core.num.U32.to_le_bytes v).val := by
  apply List.ext_getElem
  · simp [wordBytes, core.num.U32.to_le_bytes, BitVec.toLEBytes]
  · intro i hi hj
    have hib : i < 4 := by simpa [wordBytes] using hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;>
      apply UScalar.eq_of_val_eq <;>
      simp [wordBytes,core.num.U32.to_le_bytes,BitVec.toLEBytes,
        UScalar.cast_val_eq,U32.wrapping_shr_bv_eq,UScalar.val,
        BitVec.toNat_setWidth,BitVec.toNat_ushiftRight]

set_option backward.isDefEq.respectTransparency false in
theorem index_bytes (v : U64) : indexBytes v = (core.num.U64.to_le_bytes v).val := by
  apply List.ext_getElem
  · simp [indexBytes, core.num.U64.to_le_bytes, BitVec.toLEBytes]
  · intro i hi hj
    have hib : i < 8 := by simpa [indexBytes] using hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply UScalar.eq_of_val_eq <;>
      simp [indexBytes,core.num.U64.to_le_bytes,BitVec.toLEBytes,
        UScalar.cast_val_eq,U64.wrapping_shr_bv_eq,UScalar.val,
        BitVec.toNat_setWidth,BitVec.toNat_ushiftRight]


#print axioms word_bytes
#print axioms index_bytes
end PV_B3P_ByteEndian226V3
