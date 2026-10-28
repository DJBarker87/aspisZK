import PV_B3P_ByteScalar226V3
import PV_B3P_ByteLayout226V3
import PV_B3P_RustResult
namespace PV_B3P_WordLaw226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult PV_B3P_ByteScalar226V3
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error

def four (v : U32) : Result (core.result.Result (List U8) E) :=
  bindR (reference226.field_byte v 0#usize) (fun b0 =>
  bindR (reference226.field_byte v 1#usize) (fun b1 =>
  bindR (reference226.field_byte v 2#usize) (fun b2 =>
  bindR (reference226.field_byte v 3#usize) (fun b3 => .ok (.Ok [b0,b1,b2,b3])))))

-- Rechecking canonicality for each byte has the same complete Result as
-- checking once before the four little-endian bytes, including rejected words.
theorem complete_word (v : U32) : four v =
    if v < 2147483647#u32 then .ok (.Ok (PV_B3P_ByteLayout226V3.wordBytes v))
    else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  have hc0 : U32.wrapping_mul 8#u32 (UScalar.cast .U32 0#usize) = 0#u32 := by rfl
  have hc1 : U32.wrapping_mul 8#u32 (UScalar.cast .U32 1#usize) = 8#u32 := by rfl
  have hc2 : U32.wrapping_mul 8#u32 (UScalar.cast .U32 2#usize) = 16#u32 := by rfl
  have hc3 : U32.wrapping_mul 8#u32 (UScalar.cast .U32 3#usize) = 24#u32 := by rfl
  have hz : U32.wrapping_shr v 0#u32 = v := by
    apply UScalar.eq_of_val_eq
    change (U32.wrapping_shr v 0#u32).bv.toNat = v.val
    rw [U32.wrapping_shr_bv_eq]
    simp [BitVec.toNat_ushiftRight]
  by_cases h : v < 2147483647#u32
  · simp only [h, ↓reduceIte, four, field_success v 0#usize h, field_success v 1#usize h,
      field_success v 2#usize h, field_success v 3#usize h, bindR,
      PV_B3P_ByteLayout226V3.wordBytes,hc0,hc1,hc2,hc3,hz]
  · simp only [h, ↓reduceIte, four, field_reject v 0#usize h, bindR]

#print axioms complete_word
end PV_B3P_WordLaw226V3
