import Aeneas
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsSubtract
open Aeneas Aeneas.Std Result

theorem wrapping_value (x y : Usize) (h : y.val ≤ x.val) :
    (Usize.wrapping_sub x y).val = x.val-y.val := by
  change (x.bv-y.bv).toNat = _
  exact BitVec.toNat_sub_of_le h

theorem checked (x y : Usize) (h : y.val ≤ x.val) :
    UScalar.sub x y = ok (Usize.wrapping_sub x y) := by
  unfold UScalar.sub
  rw [if_neg (by omega)]
  apply congrArg ok
  apply UScalar.eq_of_val_eq
  change (x.val-y.val)%2^(UScalarTy.numBits .Usize) = (Usize.wrapping_sub x y).val
  rw [wrapping_value x y h]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.bv.isLt)
#print axioms wrapping_value
#print axioms checked
end R1Z.PV_CB3_WeightsSubtract
