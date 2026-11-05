import NGW_Usize
set_option autoImplicit false
namespace NGW_KindIndex
open Aeneas Aeneas.Std

theorem bound (k : Usize) (hk : k.val<2) : (Usize.wrapping_add 3#usize k).val<5 := by
 have size : 4096≤UScalar.size .Usize := by
  rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h|h <;> simp [h]
 rw [Usize.wrapping_add_val_eq]
 change (3+k.val)%UScalar.size .Usize<5
 rw [Nat.mod_eq_of_lt (by omega)]
 omega

#print axioms bound
end NGW_KindIndex
