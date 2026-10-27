import R1Z.PV_CB3_WeightsBits
import Aeneas
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsMachine
open Aeneas Aeneas.Std

theorem width_min : 32 ≤ UScalarTy.numBits .Usize := by
  rcases System.Platform.numBits_eq with h|h <;> simp [UScalarTy.numBits,h]

theorem cast_count (x : Usize) (h : x.val < 32) :
    (UScalar.cast .U32 x).val = x.val := by
  change (BitVec.zeroExtend 32 x.bv).toNat = _
  rw [BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by change x.val < 4294967296; omega)

theorem shift_left (x : Usize) (count : U32) (hx : x.val < 4) (hc : count.val ≤ 8) :
    (Usize.wrapping_shl x count).val = x.val * 2^count.val := by
  change (x.val <<< (count.val % UScalarTy.numBits .Usize)) % 2^(UScalarTy.numBits .Usize) = _
  have hw := width_min
  rw [Nat.mod_eq_of_lt (by omega : count.val < UScalarTy.numBits .Usize),Nat.shiftLeft_eq]
  have hb := PV_CB3_WeightsBits.shifted_bound x.val count.val hx hc
  rw [Nat.shiftLeft_eq] at hb
  have hp : 2^10 ≤ 2^(UScalarTy.numBits .Usize) := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb hp)

theorem shift_right (x : Usize) (count : U32) (hc : count.val < 10) :
    (Usize.wrapping_shr x count).val = x.val / 2^count.val := by
  change (x.val >>> (count.val % UScalarTy.numBits .Usize)) = _
  have hw := width_min
  rw [Nat.mod_eq_of_lt (by omega : count.val < UScalarTy.numBits .Usize),Nat.shiftRight_eq_div_pow]
#print axioms width_min
#print axioms cast_count
#print axioms shift_left
#print axioms shift_right
end R1Z.PV_CB3_WeightsMachine
