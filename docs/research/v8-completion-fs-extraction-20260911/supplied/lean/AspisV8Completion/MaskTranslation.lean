/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.MaskTranslation
noncomputable section

/-- Translation is a bijection, the algebraic core of additive-mask hiding.
This is NOT a simulator for the joint adaptive transcript/commitment view. -/
def shiftEquiv (F : Type*) [AddGroup F] (delta : F) : F ≃ F where
  toFun x := x+delta
  invFun x := x-delta
  left_inv x := by simp
  right_inv x := by simp

/-- A linear image of mask translations can absorb the witness-view shift.
The actual selected mask map must supply delta for EVERY allowed witness pair. -/
theorem shifted_view_equal {R V U : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup U] [Module R U]
    (L : V →ₗ[R] U) (delta mask : V) (left right : U)
    (absorbs : L delta = left-right) :
    L (mask+delta)+right = L mask+left := by
  rw [map_add, absorbs]
  abel

/-- Finite uniform masks remain uniform after a fixed translation. -/
theorem uniform_translation_sum {F : Type*} [AddGroup F] [Fintype F]
    (delta : F) (payoff : F → ℚ) :
    (∑ mask, payoff (mask+delta)) = ∑ mask, payoff mask := by
  exact Equiv.sum_comp (shiftEquiv F delta) payoff

#print axioms shifted_view_equal
#print axioms uniform_translation_sum
end
end AspisV8Completion.MaskTranslation
