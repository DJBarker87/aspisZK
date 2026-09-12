/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.TransferAmounts

structure Amounts where
  input : Nat
  recipient : Nat
  change : Nat

def valid (a : Amounts) : Prop :=
  a.input < 2^30 ∧ a.recipient < 2^30 ∧ a.change < 2^30 ∧
  0 < a.recipient ∧ 0 < a.change ∧ a.input = a.recipient+a.change

instance (a : Amounts) : Decidable (valid a) := by unfold valid; infer_instance

def check (a : Amounts) : Bool := decide (valid a)

theorem check_sound (a : Amounts) (ok : check a=true) : valid a := by
  exact of_decide_eq_true ok

/-- Range and conservation are over integers/Nat, not just modulo M31. -/
theorem no_wraparound (p input recipient change : Nat)
    (pPositive : 0 < p) (inputRange : input < p)
    (sumRange : recipient+change < p)
    (fieldEquation : input % p = (recipient+change) % p) :
    input = recipient+change := by
  simpa [Nat.mod_eq_of_lt inputRange, Nat.mod_eq_of_lt sumRange] using fieldEquation

/-- The inverse-product residual implies nonzero factors in any field.
It does not by itself establish positive integers or canonical descent. -/
theorem inverse_product_nonzero {F : Type*} [Field F] (x y inverse : F)
    (residual : (x*y)*inverse=1) : x≠0 ∧ y≠0 := by
  constructor
  · intro zero
    simp [zero] at residual
  · intro zero
    simp [zero] at residual

#print axioms no_wraparound
#print axioms inverse_product_nonzero
end AspisV8Completion.TransferAmounts
