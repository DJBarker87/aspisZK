import R1Z.PV_RDEAC_ActualRound
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDEAC_NibbleBounds
theorem high_bound (b : U8) :
    (UScalar.cast .Usize (U8.wrapping_shr b 4#u32)).val<16 := by
  change (BitVec.setWidth UScalarTy.Usize.numBits (b.bv >>> 4)).toNat<16
  rw [BitVec.toNat_setWidth]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.toNat_ushiftRight_lt b.bv 4 (by decide))

theorem low_bound (b : U8) : (UScalar.cast .Usize (b &&& 15#u8)).val<16 := by
  change (BitVec.setWidth UScalarTy.Usize.numBits (b.bv &&& (15#8))).toNat<16
  rw [BitVec.toNat_setWidth,BitVec.toNat_and]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (lt_of_le_of_lt Nat.and_le_right (by decide))

#print axioms high_bound
#print axioms low_bound
end R1Z.PV_RDEAC_NibbleBounds
