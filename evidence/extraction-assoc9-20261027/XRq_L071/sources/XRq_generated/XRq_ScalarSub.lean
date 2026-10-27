import XRq_AddValue
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace XRq_ScalarSub
open XRp_PowersScalarSub
/-- Split replacement for XRp_L095; no failed source is rerun unchanged. -/
theorem sub (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
 XRn_Join_Field.field.M31.sub a b = AspisR1Qm31ArithmeticProbe.field.M31.sub a b := by
 rw [source,target]
 rw [XRp_CheckedWrapping.add a 2147483647#u32 (by scalar_tac)]
 change wrappingSub (U32.wrapping_add a 2147483647#u32) b =
   checkedSub (U32.wrapping_add a 2147483647#u32) b
 exact subtract _ _ (XRq_AddValue.offset_bound a b ha hb)
#print axioms sub
end XRq_ScalarSub
