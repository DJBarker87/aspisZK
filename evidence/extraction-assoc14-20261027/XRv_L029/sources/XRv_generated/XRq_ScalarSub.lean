import XRq_SubCompose
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace XRq_ScalarSub
open XRp_PowersScalarSub
/-- Split replacement for XRp_L095; no failed source is rerun unchanged. -/
theorem sub (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
 XRn_Join_Field.field.M31.sub a b = AspisR1Qm31ArithmeticProbe.field.M31.sub a b := by
 exact (source a b).trans
   ((XRq_SubCompose.compose a b 2147483647#u32 (by scalar_tac)
     (XRq_AddValue.offset_bound a b ha hb)).trans (target a b).symm)
#print axioms sub
end XRq_ScalarSub
