import PCD_LaneRef.Funs
set_option autoImplicit false
namespace PCD_ArrayEq
open Aeneas Aeneas.Std
/-- Structural induction, never concrete reduction over the whole frontier. -/
theorem zipped_equal {α : Type} [DecidableEq α] (xs ys : List α)
    (sameLength : xs.length = ys.length) :
    List.allM (fun pair : α × α => (Result.ok (decide (pair.1 = pair.2)))) (xs.zip ys) =
      (Result.ok (decide (xs = ys))) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at sameLength
  | cons x xs ih =>
    cases ys with
    | nil => simp at sameLength
    | cons y ys =>
      have len : xs.length = ys.length := by simpa using sameLength
      by_cases h : x = y
      · subst y
        simp [List.allM, ih ys len]
      · simp [List.allM, h]
        rfl
#print axioms zipped_equal
end PCD_ArrayEq
