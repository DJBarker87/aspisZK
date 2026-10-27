import FJj_KindScaleTrace
set_option autoImplicit false
namespace AspisR1.FJr_KindIndices
open Aeneas Aeneas.Std

theorem sub (a b : Usize) (ha : a.val<16) (hb : b.val≤a.val) :
    (Usize.wrapping_sub a b).val=a.val-b.val := by
  have size : 16≤UScalar.size .Usize := by
    rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h|h <;> simp [h]
  rw [Usize.wrapping_sub_val_eq,
    show a.val+(UScalar.size .Usize-b.val)=a.val-b.val+UScalar.size .Usize by omega,
    Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem five : Usize.wrapping_sub 5#usize 2#usize=3#usize := by
  apply UScalar.eq_of_val_eq
  rw [sub _ _ (by decide) (by decide)]
  rfl

theorem six : Usize.wrapping_sub 6#usize 2#usize=4#usize := by
  apply UScalar.eq_of_val_eq
  rw [sub _ _ (by decide) (by decide)]
  rfl

#print axioms sub
#print axioms five
#print axioms six
end AspisR1.FJr_KindIndices
