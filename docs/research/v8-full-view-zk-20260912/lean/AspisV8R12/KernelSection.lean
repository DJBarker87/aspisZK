import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Abel
set_option autoImplicit false
namespace AspisV8R12
variable {K U A B : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
noncomputable def kernelSectionEquiv
    (old : U →ₗ[K] A) (next : U →ₗ[K] B) (lift : B →ₗ[K] U)
    (preserves : ∀ b, old (lift b) = 0) (covers : ∀ b, next (lift b) = b) :
    {u : U // old u = 0} ≃ B × {u : U // old u = 0 ∧ next u = 0} where
  toFun u := (next u.1, ⟨u.1-lift (next u.1), by
    constructor
    · simp [u.2, preserves]
    · simp [covers]⟩)
  invFun y := ⟨lift y.1+y.2.1, by simp [preserves, y.2.2.1]⟩
  left_inv u := by apply Subtype.ext; change lift (next u.1) + (u.1-lift (next u.1)) = u.1; abel
  right_inv y := by
    rcases y with ⟨b, u⟩; apply Prod.ext
    · simp [covers, u.2.2]
    · apply Subtype.ext; simp only [map_add, covers, u.2.2, add_zero]; abel
#print axioms kernelSectionEquiv
end AspisV8R12
