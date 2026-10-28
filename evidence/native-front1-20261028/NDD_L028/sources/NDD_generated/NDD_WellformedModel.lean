import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_WellformedModel
/-- Induction for the translated library allM, with the actual total per-element
predicate law explicit; neither a whole-buffer native run nor a new caller join. -/
theorem allM_total {α : Type} (predicate : α → Result Bool) (test : α → Bool)
    (law : ∀ x, predicate x = ok (test x)) (xs : List α) :
    xs.allM predicate = ok (xs.all test) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.allM,List.all,law,ih]
#print axioms allM_total
end NDD_WellformedModel
