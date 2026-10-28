import Aeneas
set_option autoImplicit false
namespace PV_B2_D_SmallScalar
open Aeneas Aeneas.Std

theorem size_bound : 1024 < UScalar.size .Usize := by
  rw [UScalar.size]
  change 1024 < 2^System.Platform.numBits
  have h : 2^32 ≤ 2^System.Platform.numBits :=
    Nat.pow_le_pow_right (by decide) System.Platform.le_numBits
  omega

theorem cast_val {ty : UScalarTy} (x : UScalar ty) (tgt : UScalarTy) :
    (UScalar.cast tgt x).val = x.val % 2^tgt.numBits := by
  simp only [UScalar.cast,UScalar.val,BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth]

theorem add_val (a b : Usize) (h : a.val+b.val < 1024) :
    (Usize.wrapping_add a b).val = a.val+b.val := by
  rw [Usize.wrapping_add_val_eq]
  exact Nat.mod_eq_of_lt (lt_trans h size_bound)

theorem mul_val (a b : Usize) (h : a.val*b.val < 1024) :
    (Usize.wrapping_mul a b).val = a.val*b.val := by
  rw [Usize.wrapping_mul_val_eq]
  exact Nat.mod_eq_of_lt (lt_trans h size_bound)

theorem shift_val (x : Usize) (b : U32) (hb : b.val < 32) :
    (Usize.wrapping_shl x b).val = (x.val * 2^b.val) % UScalar.size .Usize := by
  unfold Usize.wrapping_shl UScalar.wrapping_shl
  simp only [UScalar.val,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,UScalar.size]
  have h : b.val < UScalarTy.Usize.numBits := lt_of_lt_of_le hb System.Platform.le_numBits
  rw [Nat.mod_eq_of_lt h]
#print axioms size_bound
#print axioms cast_val
#print axioms add_val
#print axioms mul_val
#print axioms shift_val
end PV_B2_D_SmallScalar
