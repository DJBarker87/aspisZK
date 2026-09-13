import AspisV8H1C2.FiniteTransport
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

/-! A nonlinear witness offset needs no linearity hypothesis when an unused
fresh uniform additive pad covers its entire fixed observation image. -/
set_option autoImplicit false
namespace AspisV8H1C2
noncomputable section
variable {K U V E W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup E] [Module K E]

def padTranslation (d : U) : U ≃ U where
  toFun u := u + d
  invFun u := u - d
  left_inv u := by simp
  right_inv u := by simp

theorem covered_nonlinear_offset_pointwise
    (M : U →ₗ[K] V) (B : E →ₗ[K] V) (C : E →ₗ[K] U)
    (covers : M.comp C = B) (f : W → E) (w : W) (u : U) :
    M (u + C (f w)) = B (f w) + M u := by
  have h : M (C (f w)) = B (f w) := DFunLike.congr_fun covers (f w)
  rw [map_add, h, add_comm]

theorem covered_nonlinear_offset_uniform
    [Fintype U] [Nonempty U]
    (M : U →ₗ[K] V) (B : E →ₗ[K] V) (C : E →ₗ[K] U)
    (covers : M.comp C = B) (f : W → E) (w : W) :
    SameUniformLaw (fun u => B (f w) + M u) (fun u => M u) := by
  apply sameUniformLaw_of_equiv _ _ (padTranslation (C (f w)))
  intro u
  exact covered_nonlinear_offset_pointwise M B C covers f w u

#print axioms covered_nonlinear_offset_pointwise
#print axioms covered_nonlinear_offset_uniform
end
end AspisV8H1C2
