import NDD_Reference.Funs
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
    cases h : test x <;> simp [List.allM,List.all,law,ih,h] <;> rfl
theorem native_step_reference (old : Bool) (a b : U32) :
    NDD_Reference.wellformed_step_ref old a b = ok (old && decide (a < b)) := by
  cases old <;> rfl
#print axioms native_step_reference
#print axioms allM_total
end NDD_WellformedModel
