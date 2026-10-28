import R1Z.PV_RDEAC_ActualDigits
import R1Z.PV_RDEA_NameFill
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_NibbleModel

def byte (b : U8) : Fin 256 := ⟨b.val,by have h:=b.hSize; norm_num only [UScalar.size,UScalarTy.U8_numBits_eq] at h; exact h⟩

theorem high_val (b : U8) : (PV_RDEAC_ActualDigits.high b).val=b.val/16 := by
  change (BitVec.setWidth UScalarTy.Usize.numBits (b.bv >>> 4)).toNat=b.bv.toNat/16
  rw [BitVec.toNat_setWidth]
  have bound : (b.bv >>> 4).toNat<2^UScalarTy.Usize.numBits := by
    have h := BitVec.toNat_ushiftRight_lt b.bv 4 (by decide)
    have size := (15#usize).hSize
    simp only [UScalar.size,UScalar.ofNatCore_val_eq] at size
    omega
  rw [Nat.mod_eq_of_lt bound,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

theorem low_val (b : U8) : (PV_RDEAC_ActualDigits.low b).val=b.val%16 := by
  change (BitVec.setWidth UScalarTy.Usize.numBits (b.bv &&& (15#8))).toNat=b.bv.toNat%16
  rw [BitVec.toNat_setWidth,BitVec.toNat_and]
  change (b.bv.toNat &&& 15)%2^UScalarTy.Usize.numBits=b.bv.toNat%16
  have bound : b.bv.toNat &&& 15<2^UScalarTy.Usize.numBits := by
    have h : b.bv.toNat &&& 15≤15 := Nat.and_le_right
    have size := (15#usize).hSize
    simp only [UScalar.size,UScalar.ofNatCore_val_eq] at size
    omega
  rw [Nat.mod_eq_of_lt bound]
  exact Nat.and_two_pow_sub_one_eq_mod _ 4

theorem high (b : U8) : PV_RDEAC_ActualDigits.high b=PV_RDEA_ReservationName.high (byte b) := by
  apply Fin.ext
  exact high_val b

theorem low (b : U8) : PV_RDEAC_ActualDigits.low b=PV_RDEA_ReservationName.low (byte b) := by
  apply Fin.ext
  exact low_val b

#print axioms high_val
#print axioms low_val
#print axioms high
#print axioms low
end R1Z.PV_RDEAC_NibbleModel
