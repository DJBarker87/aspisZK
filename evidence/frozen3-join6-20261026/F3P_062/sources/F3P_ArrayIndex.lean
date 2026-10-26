import F3P_DecodeCircleCell
set_option autoImplicit false
namespace AspisR1.F3P_ArrayIndex
open Aeneas Aeneas.Std Result

theorem cell {A : Type} {n : Usize} (a : Array A n) (i : Usize) (x : A)
    (h : Array.index_usize a i=ok x) :
    ∃ bound : i.val<a.val.length,a.val[i.val]'bound=x := by
  unfold Array.index_usize at h
  split at h
  · cases h
  · rename_i value hv
    change a.val[i.val]?=some value at hv
    obtain ⟨bound,same⟩ := List.getElem?_eq_some_iff.mp hv
    exact ⟨bound,same.trans (Result.ok.inj h)⟩

#print axioms cell
end AspisR1.F3P_ArrayIndex
