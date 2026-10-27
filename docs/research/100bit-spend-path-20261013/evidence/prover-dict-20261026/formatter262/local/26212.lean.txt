import R1Z.PDict_OwnedCell262
set_option autoImplicit false
namespace R1Z.PDict_RowBits262
open Aeneas Aeneas.Std

/-- A two-bit digit is bounded regardless of the input machine word. -/
theorem digit_bound (j : Usize) : (j &&& 3#usize).val < 4 := by
  rw [UScalar.val_and]
  have three : (3#usize).val = 3 := by scalar_tac
  rw [three]
  exact Nat.and_lt_two_pow j.val (by decide : 3 < 2^2)

/-- All shifts used by the row permutation remain below ten bits. -/
theorem shifted_bound (x : Usize) (digit : x.val < 4)
    (shift : U32) (small : shift.val ≤ 8) :
    (Usize.wrapping_shl x shift).val < 1024 := by
  change (x.bv <<< (shift.val % UScalarTy.Usize.numBits)).toNat < 1024
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have exponent : shift.val % UScalarTy.Usize.numBits ≤ 8 :=
    (Nat.mod_le _ _).trans small
  have power : 2^(shift.val % UScalarTy.Usize.numBits) ≤ 256 :=
    Nat.pow_le_pow_right (by decide) exponent
  have value : x.bv.toNat = x.val := rfl
  rw [value]
  have multiply : x.val * 2^(shift.val % UScalarTy.Usize.numBits) < 1024 :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ power) (by omega)
  exact lt_of_le_of_lt (Nat.mod_le _ _) multiply

theorem shifted_digit_bound (j : Usize) (shift : U32) (small : shift.val ≤ 8) :
    (Usize.wrapping_shl (j &&& 3#usize) shift).val < 1024 :=
  shifted_bound _ (digit_bound j) shift small

/-- Bitwise union preserves the ten-bit bound; no positional case split. -/
theorem union_bound (x y : Usize) (hx : x.val < 1024) (hy : y.val < 1024) :
    (x ||| y).val < 1024 := by
  rw [UScalar.val_or]
  exact Nat.or_lt_two_pow (n := 10) hx hy

#print axioms digit_bound
#print axioms shifted_bound
#print axioms shifted_digit_bound
#print axioms union_bound
end R1Z.PDict_RowBits262
