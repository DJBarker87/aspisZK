import NJH_Ref.Funs
import S2TrustedSdkBorrow
set_option autoImplicit false
namespace NJH_BorrowLaws
open Aeneas Aeneas.Std Result
/-- Successful extracted acquisition, before interpreting the signed counter. -/
theorem shared_ok (x : I64) (lo : x ≥ 0#i64) (hi : x < core.num.I64.MAX) :
    NJH_Ref.shared_ref x = ok (.Ok (I64.wrapping_add x 1#i64)) := by
  simp only [NJH_Ref.shared_ref, if_pos lo, if_pos hi]
  rfl
theorem shared_negative (x : I64) (h : ¬ x ≥ 0#i64) :
    NJH_Ref.shared_ref x = ok (.Err ()) := by
  simp only [NJH_Ref.shared_ref, if_neg h]
theorem shared_saturated (x : I64) (lo : x ≥ 0#i64) (h : ¬ x < core.num.I64.MAX) :
    NJH_Ref.shared_ref x = ok (.Err ()) := by
  simp only [NJH_Ref.shared_ref, if_pos lo, if_neg h]
theorem exclusive_ok : NJH_Ref.exclusive_ref 0#i64 = ok (.Ok (-1)#i64) := rfl
theorem exclusive_error (x : I64) (h : x ≠ 0#i64) :
    NJH_Ref.exclusive_ref x = ok (.Err ()) := by
  simp only [NJH_Ref.exclusive_ref, if_neg h]
theorem exclusive_drop : NJH_Ref.exclusive_drop_ref = ok 0#i64 := rfl
#print I64.wrapping_add_val_eq
#print I64.wrapping_sub_val_eq
#print axioms shared_ok
#print axioms shared_negative
#print axioms shared_saturated
#print axioms exclusive_ok
#print axioms exclusive_error
#print axioms exclusive_drop
end NJH_BorrowLaws
