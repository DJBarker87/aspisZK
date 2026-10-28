import PV_B3_SparseArray
namespace PV_B3_SparseSet
open Aeneas Aeneas.Std Result PV_B3_SparseArray
set_option autoImplicit false
variable {A : Type}

theorem set (size : Usize) (xs : Nat → A) (i : Usize) (z : A) :
    Array.set (array size xs) i z = array size (Function.update xs i.val z) := by
  apply Subtype.ext
  change (array size xs).val.set i.val z =
    (array size (Function.update xs i.val z)).val
  apply List.ext_getElem
  · simp only [List.length_set, array, List.length_ofFn]
  · intro k hk1 hk2
    simp only [array, List.getElem_set, List.getElem_ofFn]
    by_cases h : k = i.val
    · subst k; simp only [Function.update_self, if_true]
    · simp only [Ne.symm h, if_false, Function.update_of_ne h]

theorem mutable_index (size : Usize) (xs : Nat → A) (i : Usize)
    (hi : i.val < size.val) :
    Array.index_mut_usize (array size xs) i =
      ok (xs i.val, fun z => array size (Function.update xs i.val z)) := by
  unfold Array.index_mut_usize
  rw [index size xs i hi]
  simp only [bind_tc_ok]
  congr 1
  funext z
  exact set size xs i z

#print axioms set
#print axioms mutable_index
end PV_B3_SparseSet
