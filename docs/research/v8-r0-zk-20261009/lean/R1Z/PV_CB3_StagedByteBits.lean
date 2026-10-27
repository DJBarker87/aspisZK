import R1Z.PV_CB3_StagedLoadInspect
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedByteBits
open Aeneas Aeneas.Std

theorem shift_value {w : Nat} (x : BitVec w) (h : x.toNat * 256 < 2^w) :
    (x <<< 8).toNat = x.toNat * 256 := by
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt h

theorem or_low {w : Nat} (lo : BitVec 8) (right : BitVec w) (hw : 8 ≤ w)
    (hi : Nat) (hr : right.toNat = 256 * hi) :
    ((lo.setWidth w) ||| right).toNat = lo.toNat + 256 * hi := by
  rw [BitVec.toNat_or,BitVec.toNat_setWidth_of_le hw,hr,Nat.or_comm]
  rw [← Nat.two_pow_add_eq_or_of_lt lo.isLt]
  omega
#print axioms shift_value
#print axioms or_low
end R1Z.PV_CB3_StagedByteBits
