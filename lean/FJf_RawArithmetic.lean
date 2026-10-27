import FJf_RawReference
import JFv_TX2_FoldValue
set_option autoImplicit false
namespace AspisR1.FJf_RawArithmetic
open Aeneas Aeneas.Std
open FJf_RawReference

theorem add_value (a b : U64) (h : a.val+b.val < UScalar.size .U64) :
    (add a b).val=a.val+b.val := by rw [U64.wrapping_add_val_eq,Nat.mod_eq_of_lt h]

theorem sub_value (a b : U64) (h : b.val≤a.val) : (sub a b).val=a.val-b.val := by
  rw [U64.wrapping_sub_val_eq]
  have ha := a.hSize
  have hb := b.hSize
  rw [show a.val+(UScalar.size .U64-b.val)=(a.val-b.val)+UScalar.size .U64 by omega,
    Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem mul_value (a b : U64) (h : a.val*b.val < UScalar.size .U64) :
    (mul a b).val=a.val*b.val := by rw [U64.wrapping_mul_val_eq,Nat.mod_eq_of_lt h]

theorem product_value (a b : U32) : (product a b).val=a.val*b.val := by
  unfold product
  rw [U64.wrapping_mul_val_eq,JFr_TX2_DotLaneTotal.extend,JFr_TX2_DotLaneTotal.extend]
  have ha := a.hSize
  have hb := b.hSize
  apply Nat.mod_eq_of_lt
  norm_num [UScalar.size,UScalarTy.numBits,U32.size,U32.numBits,U64.size,U64.numBits] at ha hb ⊢
  nlinarith

theorem product_bound (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    a.val*b.val≤4611686014132420609 := by
  have h := Nat.mul_le_mul (by omega : a.val≤2147483647) (by omega : b.val≤2147483647)
  exact h

#print axioms add_value
#print axioms sub_value
#print axioms mul_value
#print axioms product_value
#print axioms product_bound
end AspisR1.FJf_RawArithmetic
