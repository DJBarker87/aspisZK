import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace NEX_FirstError
open Aeneas Aeneas.Std
variable {A E : Type}
/-- A native decoder stops at the first error. Replies after it are not an
admission restriction, since the caller never asks for them. -/
def first : List (core.result.Result A E) → Nat
 | [] => 0
 | .Err _ :: _ => 0
 | .Ok _ :: xs => 1+first xs

theorem bounded (xs : List (core.result.Result A E)) : first xs≤xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [first,List.length_cons] <;> omega

theorem before (xs : List (core.result.Result A E)) (i : Nat) (hi : i<first xs) :
    ∃ a, xs[i]?=some (.Ok a) := by
  induction xs generalizing i with
  | nil => simp only [first] at hi; omega
  | cons x xs ih =>
    cases x with
    | Err e => simp only [first] at hi; omega
    | Ok a =>
      cases i with
      | zero => exact ⟨a,rfl⟩
      | succ i =>
        have bound : i<first xs := by simp only [first] at hi; omega
        exact ih i bound

theorem at_error (xs : List (core.result.Result A E)) (hi : first xs<xs.length) :
    ∃ e, xs[first xs]?=some (.Err e) := by
  induction xs with
  | nil => simp only [first,List.length_nil] at hi; omega
  | cons x xs ih =>
    cases x with
    | Err e => exact ⟨e,rfl⟩
    | Ok a =>
      have bound : first xs<xs.length := by simp only [first,List.length_cons] at hi; omega
      simpa only [first, Nat.add_comm 1, List.getElem?_cons_succ] using ih bound

#print axioms bounded
#print axioms before
#print axioms at_error
end NEX_FirstError
