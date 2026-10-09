/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.FirstExposure
variable {I O : Type*} [DecidableEq I]

structure Call (I O : Type*) where
  input : I
  output : O

/-- An explicit earliest occurrence; no arbitrary successful trial can stand
in for the actual accepted transcript's first exposure. -/
def FirstAt (trace : List (Call I O)) (input : I) (i : Nat) : Prop :=
  ∃ event, trace[i]? = some event ∧ event.input = input ∧
    ∀ j, j < i → ∀ prior, trace[j]? = some prior → prior.input ≠ input

theorem first_unique (trace : List (Call I O)) (input : I) (i j : Nat)
    (hi : FirstAt trace input i) (hj : FirstAt trace input j) : i=j := by
  obtain ⟨ei,atI,inputI,beforeI⟩ := hi
  obtain ⟨ej,atJ,inputJ,beforeJ⟩ := hj
  by_contra ne
  rcases lt_or_gt_of_ne ne with less | greater
  · exact (beforeJ i less ei atI) inputI
  · exact (beforeI j greater ej atJ) inputJ

/-- The selected target must already be a function of the strict prefix.
This identity does not prove that a protocol target has that representation. -/
def targetAt (make : List (Call I O) → I → Finset O)
    (trace : List (Call I O)) (i : Nat) (input : I) : Finset O :=
  make (trace.take i) input

theorem target_prefix_stable (make : List (Call I O) → I → Finset O)
    (left right : List (Call I O)) (i : Nat) (input : I)
    (same : left.take i = right.take i) :
    targetAt make left i input = targetAt make right i input := by
  simp only [targetAt, same]

#print axioms first_unique
end AspisV8Completion.FirstExposure
