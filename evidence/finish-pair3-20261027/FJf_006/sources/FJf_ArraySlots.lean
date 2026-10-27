import FJf_ArrayOps
set_option autoImplicit false
namespace AspisR1.FJf_ArraySlots
open Aeneas Aeneas.Std Result

theorem set_slot {A : Type} {N : Usize} (a : Array A N) (i : Usize) (x : A)
    (hi : i.val<a.val.length) (j : Nat) :
    (a.set i x).val[j]?=if i.val=j then some x else a.val[j]? := by
  rw [FJf_ArrayOps.set_val,List.getElem?_set]
  by_cases h : i.val=j
  · have hj : j<a.val.length := h ▸ hi
    simp only [h,if_pos hj,if_true]
  · simp only [h,if_false]

theorem update_slot {A : Type} {N : Usize} (a b : Array A N) (i : Usize) (x : A)
    (run : Array.update a i x=ok b) (j : Nat) :
    b.val[j]?=if i.val=j then some x else a.val[j]? := by
  have hv := FJf_ArrayOps.update_val a b i x run
  have hi : i.val<a.val.length := by
    unfold Array.update at run
    split at run
    · cases run
    · rename_i v h
      exact (List.getElem_of_getElem? h).choose
  rw [hv,←FJf_ArrayOps.set_val a i x]
  exact set_slot a i x hi j
#print axioms set_slot
#print axioms update_slot
end AspisR1.FJf_ArraySlots
