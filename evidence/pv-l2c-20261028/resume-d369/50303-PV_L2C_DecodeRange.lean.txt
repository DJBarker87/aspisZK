import PV_L2C_CanonicalParser
set_option autoImplicit false
namespace PV_L2C_DecodeRange
open Aeneas Aeneas.Std Result PV_CB_ShippedOp71

/-- Complete return, including the rejecting option, of the extracted scalar
decoder. No assumption about the byte representation is used. -/
theorem scalar_result (bytes : Array U8 4#usize) :
    aspis_core.field.M31.from_le_bytes bytes =
      ok (if (core.num.U32.from_le_bytes bytes).val < 2147483647
        then some (core.num.U32.from_le_bytes bytes) else none) := by
  unfold aspis_core.field.M31.from_le_bytes
  simp only [lift, bind_tc_ok]
  split_ifs <;> simp_all [aspis_core.field.P] <;> scalar_tac
#print axioms scalar_result

theorem scalar_success (bytes : Array U8 4#usize) (v : U32)
    (h : aspis_core.field.M31.from_le_bytes bytes = ok (some v)) :
    v.val < 2147483647 := by
  rw [scalar_result] at h
  split_ifs at h with hb
  · cases h
    exact hb
  · cases h
#print axioms scalar_success

theorem rejects_P : aspis_core.field.M31.from_le_bytes
    (core.num.U32.to_le_bytes 2147483647#u32) = ok none := by
  rw [scalar_result, PV_L2C_CanonicalParser.word_roundtrip]
  rfl
#print axioms rejects_P
end PV_L2C_DecodeRange
