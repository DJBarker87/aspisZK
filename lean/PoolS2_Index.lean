import PoolS2_UniqueSource
set_option autoImplicit false
namespace AspisR1.PoolS2_Index
open Aeneas Aeneas.Std Result

theorem increment {T : Type} (items : Slice T) (i : Usize)
    (within : i < Slice.len items) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  have size := items.property
  have range : i.val + 1 ≤ Usize.max := by scalar_tac
  rw [Usize.wrapping_add_val_eq]
  have strict : i.val + (1#usize).val < UScalar.size .Usize := by
    simp only [UScalar.size,UScalarTy.numBits,Usize.max,Usize.numBits] at range ⊢
    scalar_tac
  rw [Nat.mod_eq_of_lt strict]
  rfl

theorem read {T : Type} (items : Slice T) (i : Usize)
    (within : i.val < items.val.length) :
    Slice.index_usize items i = ok (items.val[i.val]'within) := by
  simp [Slice.index_usize,Slice.getElem?_Usize_eq,within]

#print axioms increment
#print axioms read
end AspisR1.PoolS2_Index
