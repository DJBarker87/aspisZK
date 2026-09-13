import Mathlib.Algebra.Module.Equiv.Defs
import AspisV8R11.TriangularCut

set_option autoImplicit false
namespace AspisV8R11
variable {K U V : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

def coordinatesOfTwoProducts (A : U →ₗ[K] V) (R : V →ₗ[K] U)
    (left : ∀ u, R (A u) = u) (right : ∀ v, A (R v) = v) : U ≃ₗ[K] V where
  toLinearMap := A
  invFun := R
  left_inv := left
  right_inv := right

theorem checked_correction_all_targets (A : U →ₗ[K] V) (R : V →ₗ[K] U)
    (right : ∀ v, A (R v) = v) (target : V) : A (R target) = target :=
  right target

#print axioms coordinatesOfTwoProducts
#print axioms checked_correction_all_targets
end AspisV8R11
