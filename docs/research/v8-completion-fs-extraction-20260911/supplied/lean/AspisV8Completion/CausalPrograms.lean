/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.CausalPrograms
variable {Message Coin : Type*}

/-- A finite interaction syntax. Future coins are unavailable at request
construction. This is not obtained by closing over a completed transcript. -/
inductive Program (Message Coin : Type*) : Nat → Type
  | stop : Program Message Coin 0
  | ask {n : Nat} (message : Message) (next : Coin → Program Message Coin n) :
      Program Message Coin (n+1)

def execute : {n : Nat} → Program Message Coin n → (Fin n → Coin) → List (Message × Coin)
  | 0, .stop, _ => []
  | n+1, .ask message next, coins =>
      (message, coins 0) :: execute (next (coins 0)) (fun i => coins i.succ)

theorem execute_length : ∀ {n : Nat} (p : Program Message Coin n) coins,
    (execute p coins).length = n := by
  intro n p
  induction p with
  | stop => intro coins; rfl
  | ask message next ih =>
    intro coins
    simp only [execute, List.length_cons]
    rw [ih]

/-- The first message cannot depend on even its own response coin. -/
theorem first_message_fixed {n : Nat} (message : Message)
    (next : Coin → Program Message Coin n) (left right : Fin (n+1) → Coin) :
    ((execute (.ask message next) left).head?).map Prod.fst =
      ((execute (.ask message next) right).head?).map Prod.fst := by
  rfl

/-- Prefix theorem across all continuations. Key producer obligation: the
same Program must arise from the same prior adversary/source state. -/
theorem execute_take_equal : ∀ {n : Nat} (p : Program Message Coin n)
    (left right : Fin n → Coin) (cut : Nat),
    (∀ i : Fin n, i.val < cut → left i = right i) →
    (execute p left).take cut = (execute p right).take cut := by
  intro n p
  induction p with
  | stop => intro left right cut agree; rfl
  | @ask n message next ih =>
    intro left right cut agree
    cases cut with
    | zero => simp
    | succ cut =>
      have first : left 0 = right 0 := agree 0 (by simp)
      simp only [execute, List.take_succ_cons]
      rw [first]
      congr 1
      apply ih (right 0) (fun i => left i.succ) (fun i => right i.succ) cut
      intro i inside
      exact agree i.succ (by simpa using Nat.succ_lt_succ inside)

#print axioms execute_take_equal
end AspisV8Completion.CausalPrograms
