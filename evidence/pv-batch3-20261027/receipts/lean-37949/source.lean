import PV_B3_MaskSparseStep
namespace PV_B3_MaskSparseScalar
open Aeneas Aeneas.Std PV_B3_MaskSparseStep
set_option autoImplicit false
#print UScalar.wrapping_shr
#print Usize.wrapping_shr
#print Usize.wrapping_add
#print UScalar.cast_val_eq

theorem block_value (p : Usize) : (block p).val = p.val / 16 := by
  have h4 : 4 < UScalarTy.Usize.numBits := by
    change 4 < System.Platform.numBits
    have h := System.Platform.le_numBits
    omega
  unfold block Usize.wrapping_shr UScalar.wrapping_shr
  change (p.bv.ushiftRight (4 % UScalarTy.Usize.numBits)).toNat = p.val / 16
  rw [Nat.mod_eq_of_lt h4]
  change (p.bv.toNat >>> 4) = p.val / 16
  rw [UScalar.bv_toNat, Nat.shiftRight_eq_div_pow]

theorem next_value (i : Usize) (h : i.val + 1 < Usize.size) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  simp only [Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
  change (i.val + 1) % Usize.size = i.val + 1
  exact Nat.mod_eq_of_lt h

#print axioms next_value
#print axioms block_value
end PV_B3_MaskSparseScalar
