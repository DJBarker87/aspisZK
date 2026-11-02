import R1Z.PV_RunJoin_MultilinearSuffix69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MultilinearRows69
open Aeneas Aeneas.Std

theorem complete (prefix suffix trailing : Usize) (p : Nat)
    (hp : prefix.val<2^p) (ht : p+trailing.val=10) (hs : suffix.val<2^trailing.val) :
    ((Usize.wrapping_shl prefix (UScalar.cast .U32 trailing)) ||| suffix).val<1024 := by
  have small : trailing.val≤10 := by omega
  have cast : (UScalar.cast .U32 trailing).val=trailing.val := by scalar_tac
  change ((Usize.wrapping_shl prefix (UScalar.cast .U32 trailing)) ||| suffix).bv.toNat<2^10
  rw [UScalar.bv_or,BitVec.toNat_or]
  apply Nat.or_lt_two_pow
  · change (Usize.wrapping_shl prefix (UScalar.cast .U32 trailing)).val<2^10
    rw [PV_RunJoin_MultilinearBits69.shift_val _ _ (by rw [cast];omega),cast]
    have product := Nat.mul_lt_mul_of_pos_right hp (Nat.two_pow_pos trailing.val)
    rw [←Nat.pow_add,ht] at product
    exact lt_of_le_of_lt (Nat.mod_le _ _) product
  · exact lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) small)

#print axioms complete
end R1Z.PV_RunJoin_MultilinearRows69
