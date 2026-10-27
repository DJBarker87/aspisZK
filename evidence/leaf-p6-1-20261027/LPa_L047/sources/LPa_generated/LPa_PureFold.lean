import LPa_MonadicFold
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace LPa

theorem walkM_pure {A S : Type} (step : S → A → S) (xs : List A) (initial : S) :
    walkM (fun s a => ok (step s a)) xs initial = ok (xs.foldl step initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons a xs ih => simp only [walkM, bind_tc_ok, ih, List.foldl_cons]

theorem walkM_congr {A S : Type} (a b : S → A → Result S) (xs : List A) (initial : S)
    (same : ∀ s x, x ∈ xs → a s x = b s x) :
    walkM a xs initial = walkM b xs initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    have first := same initial x (by simp)
    have rest : ∀ s y, y ∈ xs → a s y = b s y := by
      intro s y hy
      exact same s y (by simp only [List.mem_cons]; exact Or.inr hy)
    simp only [walkM, first]
    congr 1
    funext next
    exact ih next rest
#print axioms walkM_pure
#print axioms walkM_congr
end LPa
