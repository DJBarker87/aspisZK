import AspisR1DecodeKFullV10.Funs
import PSem_FieldCanonical
set_option autoImplicit false
namespace AspisR1.JFv_M31
open Aeneas Aeneas.Std Result
open AspisR1DecodeKFullV10

theorem success (bytes : Array U8 4#usize)
    (canonical : (core.num.U32.from_le_bytes bytes).val < 2147483647) :
    aspis_core.field.M31.from_le_bytes bytes = ok (some (core.num.U32.from_le_bytes bytes)) := by
  unfold aspis_core.field.M31.from_le_bytes
  simp only [lift,bind_tc_ok]
  rw [if_neg (by change ¬ (2147483647:Nat) ≤ (core.num.U32.from_le_bytes bytes).val;omega)]

#print axioms success
end AspisR1.JFv_M31
