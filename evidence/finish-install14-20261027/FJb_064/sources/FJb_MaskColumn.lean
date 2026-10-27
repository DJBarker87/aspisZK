import FJb_ColumnCell
set_option autoImplicit false
namespace AspisR1.FJb_MaskColumn
open Aeneas Aeneas.Std
theorem value (i : Usize) : (i &&& 3#usize).val=i.val%4 := by
  rw [UScalar.val_and]
  change i.val &&& 3=i.val%4
  simpa using Nat.and_two_pow_sub_one_eq_mod i.val 2

theorem bound (i : Usize) : (i &&& 3#usize).val < (4#usize).val := by
  rw [value]
  exact Nat.mod_lt _ (by decide)
#print axioms value
#print axioms bound
end AspisR1.FJb_MaskColumn
