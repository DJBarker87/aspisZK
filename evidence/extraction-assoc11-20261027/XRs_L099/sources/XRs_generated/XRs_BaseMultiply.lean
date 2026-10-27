import XRs_QueryScan
import LPf_BaseMultiply
import LPh_FieldValues
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRs_BaseMultiply

theorem same_reducer (x : U64) :
 XRn_Join_Field.field.reduce_u64 x = FIo_Native.aspis_core.field.reduce_u64 x := by
 unfold XRn_Join_Field.field.reduce_u64 FIo_Native.aspis_core.field.reduce_u64
 unfold XRn_Join_Field.field.P FIo_Native.aspis_core.field.P
 rfl

theorem same_multiply (x y : U32) :
 XRn_Join_Field.field.M31.mul x y = FIo_Native.aspis_core.field.M31.mul x y := by
 simp only [XRn_Join_Field.field.M31.mul,FIo_Native.aspis_core.field.M31.mul,
  lift,bind_tc_ok,same_reducer]

theorem value (x y : U32) : ∃ z,
 XRn_Join_Field.field.M31.mul x y = ok z ∧
 z.val = (x.val*y.val)%2147483647 ∧ z.val < 2147483647 := by
 rw [same_multiply]
 exact AspisR1.LPf_BaseMultiply.source x y

theorem semantic (x y : U32) :
 XRn_Join_Field.field.M31.mul x y =
 AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x y := by
 obtain ⟨z,hz,hv,hc⟩ := value x y
 obtain ⟨w,hw,hv',hc'⟩ := AspisR1.LPh.m31_mul_value x y
 have he : z=w := UScalar.eq_of_val_eq (hv.trans hv'.symm)
 rw [hz,hw,he]
#print axioms same_reducer
#print axioms same_multiply
#print axioms value
#print axioms semantic
end XRs_BaseMultiply
