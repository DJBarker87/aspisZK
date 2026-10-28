import Aeneas.Std.SliceIter
set_option autoImplicit false
namespace R1Z.PV_RW_SliceIterator
open Aeneas Aeneas.Std Result

abbrev Iter := core.slice.iter.Iter
abbrev next := @core.slice.iter.IteratorSliceIter.next

def remaining {T : Type} (iterator : Iter T) : List T := iterator.slice.val.drop iterator.i

theorem start {T : Type} (values : Slice T) :
    core.slice.Slice.iter values = ok (⟨values,0⟩ : Iter T) := rfl

theorem next_some {T : Type} (values : Slice T) (i : Nat) (h : i < values.val.length) :
    next (⟨values,i⟩ : Iter T) = ok (some values.val[i],(⟨values,i+1⟩ : Iter T)) := by
  simp only [next,core.slice.iter.IteratorSliceIter.next]
  split
  · rfl
  · rename_i no
    exact False.elim (no h)

theorem next_none {T : Type} (values : Slice T) (i : Nat) (h : values.val.length ≤ i) :
    next (⟨values,i⟩ : Iter T) = ok (none,(⟨values,i⟩ : Iter T)) := by
  simp only [next,core.slice.iter.IteratorSliceIter.next]
  split
  · rename_i yes
    change i < values.val.length at yes
    exact False.elim (by omega)
  · rfl

theorem tail {T : Type} (values : Slice T) (i : Nat) (h : i < values.val.length) :
    remaining (⟨values,i⟩ : Iter T) = values.val[i] :: remaining (⟨values,i+1⟩ : Iter T) := by
  exact List.drop_eq_getElem_cons h

theorem exhausted {T : Type} (values : Slice T) (i : Nat) (h : values.val.length ≤ i) :
    remaining (⟨values,i⟩ : Iter T) = [] := by
  exact List.drop_eq_nil_of_le h

#print axioms start
#print axioms next_some
#print axioms next_none
#print axioms tail
#print axioms exhausted
end R1Z.PV_RW_SliceIterator
