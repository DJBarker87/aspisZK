import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel

/-! Generic two-way joint Schur equivalence.  The parametrization and
obstruction hypotheses remain explicit; this file makes no source, coverage,
privacy, or security claim. -/
set_option autoImplicit false

namespace AspisV8R19.R541

variable {F U V A B C W : Type*} [Field F]
variable [AddCommGroup U] [Module F U]
variable [AddCommGroup V] [Module F V]
variable [AddCommGroup A] [Module F A]
variable [AddCommGroup B] [Module F B]
variable [AddCommGroup C] [Module F C]
variable [AddCommGroup W] [Module F W]

/-- A complete parametrization of `ker H` and a complete obstruction test
for `range T` are exactly sufficient for the displayed joint affine system. -/
theorem joint_schur_equivalence
    (H : U →ₗ[F] A) (T : V →ₗ[F] B) (M : U →ₗ[F] B)
    (K : C →ₗ[F] U) (D : B →ₗ[F] W)
    (u0 : U) (h : A) (t0 : B)
    (hu0 : H u0 = h)
    (kernel_parametrized : LinearMap.range K = LinearMap.ker H)
    (obstruction_complete : LinearMap.ker D = LinearMap.range T) :
    (∃ u v, H u = h ∧ T v = t0 + M (u - u0)) ↔
      (∃ c, D (t0 + M (K c)) = 0) := by
  constructor
  · rintro ⟨u, v, hu, hv⟩
    have hdiff : u - u0 ∈ LinearMap.ker H := by
      change H (u - u0) = 0
      rw [map_sub, hu, hu0, sub_self]
    rw [← kernel_parametrized] at hdiff
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hdiff
    refine ⟨c, ?_⟩
    rw [hc, ← hv]
    exact D.map_zero
  · rintro ⟨c, hc⟩
    have htarget : t0 + M (K c) ∈ LinearMap.ker D := hc
    rw [obstruction_complete] at htarget
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp htarget
    have hkc_range : K c ∈ LinearMap.range K := LinearMap.mem_range.mpr ⟨c, rfl⟩
    have hkc : K c ∈ LinearMap.ker H := by
      rw [← kernel_parametrized]
      exact hkc_range
    change H (K c) = 0 at hkc
    refine ⟨u0 + K c, v, ?_, ?_⟩
    · rw [map_add, hu0, hkc, add_zero]
    · rw [hv]
      congr 1
      abel

#print axioms joint_schur_equivalence

end AspisV8R19.R541
