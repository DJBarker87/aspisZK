import NEG_RowIsolated.Funs
set_option autoImplicit false
namespace NEI_IteratorMeaning
open Aeneas Aeneas.Std Result
abbrev Iter := core.slice.iter.IterMut U64
/-- The repaired transformer interface merely composes the array and slice
borrow restorations. Its native realization is checked separately, for U64[4]. -/
theorem constructor (row : Array U64 4#usize) :
 NEG_RowIsolated.MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter row =
 ok (({slice := row.to_slice, i := 0} : Iter),
   fun transform => row.from_slice (transform {slice := row.to_slice, i := 0}).slice) := by
 rfl
/-- Arbitrary active iterator state, including the exact backward write location. -/
theorem active (it : Iter) (h : it.i < it.slice.len.val) :
 core.slice.iter.IteratorIterMut.next it =
 ok (some (it.slice[it.i]), ({slice := it.slice, i := it.i+1} : Iter),
   fun tail value => match value with
    | none => tail
    | some v => {tail with slice := tail.slice.setAtNat it.i v}) := by
 unfold core.slice.iter.IteratorIterMut.next
 rw [dif_pos h]
theorem stopped (it : Iter) (h : ¬ it.i < it.slice.len.val) :
 core.slice.iter.IteratorIterMut.next it = ok (none,it,fun tail _ => tail) := by
 unfold core.slice.iter.IteratorIterMut.next
 rw [dif_neg h]
#print axioms constructor
#print axioms active
#print axioms stopped
end NEI_IteratorMeaning
