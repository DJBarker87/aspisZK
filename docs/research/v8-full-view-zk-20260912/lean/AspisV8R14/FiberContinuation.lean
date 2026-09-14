import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Abel

/-! Correction in the existing posterior, not a new draw of earlier coins.
DRAFT: not compiled. -/
set_option autoImplicit false
namespace AspisV8R14
variable {K U V W : Type*} [Field K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

theorem posterior_projection (A : U →ₗ[K] V) (R : V →ₗ[K] U)
    (right : ∀ v, A (R v) = v) (u : U) : A (u - R (A u)) = 0 := by
  simp [map_sub, right]

theorem later_posterior_response (A : U →ₗ[K] V) (R : V →ₗ[K] U)
    (B : U →ₗ[K] W) (u : U) :
    B (u - R (A u)) = B u - B (R (A u)) := by simp

/-- Necessary AND sufficient target test in the same coin space. -/
theorem compatible_later_correction (A : U →ₗ[K] V) (B : U →ₗ[K] W)
    (R : V →ₗ[K] U) (right : ∀ v, A (R v) = v) (target : W) :
    (∃ u, A u = 0 ∧ B u = target) ↔
      ∃ z, B z - B (R (A z)) = target := by
  constructor
  · rintro ⟨u,ha,hb⟩
    refine ⟨u, ?_⟩
    simpa [ha] using hb
  · rintro ⟨z,hz⟩
    exact ⟨z-R (A z), posterior_projection A R right z, by simpa using hz⟩

#print axioms compatible_later_correction
end AspisV8R14
