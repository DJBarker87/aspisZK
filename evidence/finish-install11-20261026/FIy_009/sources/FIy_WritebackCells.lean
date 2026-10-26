import FIy_Writeback
set_option autoImplicit false
namespace AspisR1.FIy_WritebackCells
open Aeneas Aeneas.Std Result FIq_Native
open FIy_IteratorTraversal

theorem value (v : Nat → QM) (s n : Nat) (im : IterMut) (j : Nat)
    (hj : j<im.slice.val.length) :
    (deferredWrites v s n im).slice.val[j]? =
      if s≤j ∧ j<s+n then some (v j) else im.slice.val[j]? := by
  induction n generalizing s with
  | zero => simp only [deferredWrites,Nat.add_zero,if_neg (show ¬(s≤j ∧ j<s) by omega)]
  | succ n ih =>
    change ((deferredWrites v (s+1) n im).slice.val.set s (v s))[j]? = _
    by_cases he : s=j
    · subst j
      rw [List.getElem?_set_self (by rw [FIy_Writeback.length];exact hj),
        if_pos (by omega)]
    · rw [List.getElem?_set_ne he,ih]
      have h : (s+1≤j ∧ j<s+1+n) ↔ (s≤j ∧ j<s+(n+1)) := by omega
      rw [h]

theorem full (v : Nat → QM) (im : IterMut) :
    (deferredWrites v 0 im.slice.val.length im).slice.val =
      List.ofFn (fun i : Fin im.slice.val.length => v i.val) := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j<im.slice.val.length
  · rw [value v 0 _ im j hj,if_pos (by omega)]
    simp only [List.getElem?_ofFn,hj,↓reduceDIte]
  · rw [List.getElem?_eq_none (by rw [FIy_Writeback.length];omega),
      List.getElem?_eq_none (by simp only [List.length_ofFn];omega)]
#print axioms value
#print axioms full
end AspisR1.FIy_WritebackCells
