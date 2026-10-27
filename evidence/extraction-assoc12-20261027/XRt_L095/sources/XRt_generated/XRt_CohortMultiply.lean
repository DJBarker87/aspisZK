import XRs_BaseMultiply
import XRt_QueryWords
import XRt_QueryScan
import ExtractedCurrentReducer
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRt_CohortMultiply

theorem multiply (x y : U32) :
 XRn_Join_Field.field.M31.mul x y =
 AspisR1Qm31ArithmeticProbe.field.M31.mul x y := by
 obtain ⟨z,hz,hv,hc⟩ := XRs_BaseMultiply.value x y
 obtain ⟨w,hw,hv',hc'⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod x y
 have same : z = w := UScalar.eq_of_val_eq (hv.trans hv'.symm)
 rw [hz,hw,same]

theorem canonical_output (x y : U32) : ∃ z,
 XRn_Join_Field.field.M31.mul x y = ok z ∧
 AspisR1Qm31ArithmeticProbe.field.M31.mul x y = ok z ∧
 z.val = (x.val*y.val)%2147483647 ∧ z.val < 2147483647 := by
 obtain ⟨z,hz,hv,hc⟩ := XRs_BaseMultiply.value x y
 exact ⟨z,hz,(multiply x y).symm.trans hz,hv,hc⟩

#print axioms multiply
#print axioms canonical_output
end XRt_CohortMultiply
