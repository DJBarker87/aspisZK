import FIv_Arithmetic
import Mathlib.Data.Nat.Bitwise
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_SelectorIndices
open Aeneas Aeneas.Std Result WP

theorem high (row : Usize) :
    ∃ i : Usize,row >>> 4#i32=ok i ∧ i.val=row.val/16 := by
  have hy0 : 0≤(4#i32).val := by norm_num
  have hy1 : (4#i32).val<UScalarTy.Usize.numBits := by
    cases System.Platform.numBits_eq <;> norm_num [UScalarTy.Usize_numBits_eq,*]
  obtain ⟨i,run,⟨value,_⟩⟩ := WP.spec_imp_exists (UScalar.ShiftRight_IScalar_spec row (4#i32) hy0 hy1)
  refine ⟨i,run,?_⟩
  rw [value]
  simp only [IScalar.toNat,Nat.shiftRight_eq_div_pow]
  rfl

theorem low (row : Usize) : (row &&& 15#usize).val=row.val%16 := by
  rw [UScalar.val_and]
  change row.val &&& 15=row.val%16
  exact Nat.and_two_pow_sub_one_eq_mod row.val 4
#print axioms high
#print axioms low
end AspisR1.FIw_SelectorIndices
end
