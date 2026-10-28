import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD_CpopLiteral
open Aeneas Aeneas.Std
/-- Count only the three significant bits, then use the proved zero-extension
    law; never unfold the population-count recurrence at machine word width. -/
theorem four {w : Nat} (hw : 3 ≤ w) : (BitVec.ofNat w 4).cpop.toNat = 1 := by
  have he : (BitVec.ofNat 3 4).setWidth w = BitVec.ofNat w 4 :=
    BitVec.setWidth_ofNat_of_le_of_lt hw (by decide)
  rw [← he,BitVec.toNat_cpop_setWidth_eq_of_le hw]
  rfl

theorem usize_bits : (4#usize).bv = BitVec.ofNat UScalarTy.Usize.numBits 4 := by
  have hw : 3 ≤ UScalarTy.Usize.numBits := by
    simpa only [UScalarTy.numBits] using le_trans (by decide : 3 ≤ 32) System.Platform.le_numBits
  have hp : 4 < 2 ^ UScalarTy.Usize.numBits :=
    lt_of_lt_of_le (by decide : 4 < 2^3) (Nat.pow_le_pow_right (by decide) hw)
  apply BitVec.eq_of_toNat_eq
  change (4#usize).val = (BitVec.ofNat UScalarTy.Usize.numBits 4).toNat
  have hv : (4#usize).val = 4 := by scalar_tac
  rw [hv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp]

theorem usize_four : (4#usize).bv.cpop.toNat = 1 := by
  rw [usize_bits]
  apply four
  simpa only [UScalarTy.numBits] using le_trans (by decide : 3 ≤ 32) System.Platform.le_numBits
#print axioms four
#print axioms usize_bits
#print axioms usize_four
end R1Z.PV_RDCD_CpopLiteral
