import F3J_QuerySelection
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.F3K_ArrayFacts

theorem updated {α : Type} {n : Usize} (a b : Array α n) (i : Usize) (x : α)
    (h : Array.update a i x = ok b) : Array.index_usize b i = ok x := by
  unfold Array.update at h
  split at h
  · cases h
  · cases Result.ok.inj h
    simp only [Array.index_usize, Array.getElem?_Usize_eq, Array.set_val_eq]
    rename_i value hv
    have hi : i.val < a.val.length := by
      have := List.getElem?_eq_some_iff.mp hv
      exact this.1
    rw [List.getElem?_set_self hi]

theorem mutated {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (old : α) (put : α → Array α n) (x : α)
    (h : Array.index_mut_usize a i = ok (old,put)) :
    Array.index_usize (put x) i = ok x := by
  unfold Array.index_mut_usize Array.index_usize at h
  split at h
  · cases h
  · simp only [bind_tc_ok] at h
    have hp : put = Aeneas.Std.Array.set a i := (congrArg Prod.snd (Result.ok.inj h)).symm
    rw [hp]
    simp only [Array.index_usize,Array.getElem?_Usize_eq,Array.set_val_eq]
    rename_i value hv
    have hi : i.val < a.val.length := (List.getElem?_eq_some_iff.mp hv).1
    rw [List.getElem?_set_self hi]

#print axioms updated
#print axioms mutated
end AspisR1.F3K_ArrayFacts
