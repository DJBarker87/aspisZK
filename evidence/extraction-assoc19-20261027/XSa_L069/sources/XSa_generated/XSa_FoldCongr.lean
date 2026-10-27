import XSa_GenericPairs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_FoldCongr

theorem fold {A S : Type} (xs : List A) (f g : S → A → Result S)
 (h : ∀ a ∈ xs, ∀ s, f s a=g s a) (s : S) : xs.foldlM f s=xs.foldlM g s := by
 induction xs generalizing s with
 | nil => rfl
 | cons a xs ih =>
   simp only [List.foldlM_cons]
   rw [h a (by simp)]
   apply (bind_eq_iff _ _ _).mpr
   intro next hn
   exact ih (fun x hx => h x (List.mem_cons_of_mem a hx)) next

#print axioms fold
end XSa_FoldCongr
