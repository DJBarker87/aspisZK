/- Finite certificates imply a lift only for the stated linear maps.
   No universal source-prefix or shared-oracle premise is asserted here. -/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace AspisR19.H1RelationLift
variable {F V W U : Type*} [Field F]
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
variable [AddCommGroup U] [Module F U]

theorem certificate_lift {I : Type*} [Fintype I]
    (A : V →ₗ[F] W) (P : V →ₗ[F] U) (v : I → V) (b : I → U)
    (ha : ∀ i, A (v i) = 0) (hp : ∀ i, P (v i) = b i)
    (c : I → F) :
    ∃ x, A x = 0 ∧ P x = ∑ i, c i • b i := by
  refine ⟨∑ i, c i • v i, ?_, ?_⟩
  · simp only [map_sum, map_smul, ha, smul_zero, Finset.sum_const_zero]
  · simp only [map_sum, map_smul, hp]

/- Composing an earlier affine correction with a kernel correction leaves
   every earlier observation unchanged and cancels the designated polynomial. -/
theorem affine_repair (A : V →ₗ[F] W) (P : V →ₗ[F] U)
    (old pad : V) (target : W) (ho : A old = target)
    (ha : A pad = 0) (hp : P pad = -P old) :
    A (old+pad) = target ∧ P (old+pad) = 0 := by
  constructor
  · rw [map_add, ho, ha, add_zero]
  · rw [map_add, hp, add_neg_cancel]

/- Exact degree-six source polynomial after c4=-c0. -/
theorem evaluation_covector (a c0 c1 c2 c3 c5 c6 : F) :
    c0+a*(c1+a*(c2+a*(c3+a*(-c0+a*(c5+a*c6))))) =
    (1-a^4)*c0+a*c1+a^2*c2+a^3*c3+a^5*c5+a^6*c6 := by ring

/- No exceptional alpha needs to be excluded to choose a pivot. -/
theorem pivot_exists (a : F) : (1-a^4 ≠ 0) ∨ a ≠ 0 := by
  by_cases h : a=0
  · left; simp [h]
  · exact Or.inr h

/- The generic single-equation kernel has a basis obtained by solving one
   nonzero coordinate. This explicit five-coordinate form matches the checker
   after permuting the selected pivot to position zero. -/
theorem solve_pivot (e0 e1 e2 e3 e4 e5 t0 t1 t2 t3 t4 t5 : F)
    (he : e0 ≠ 0)
    (ht : e0*t0+e1*t1+e2*t2+e3*t3+e4*t4+e5*t5=0) :
    t0 = -(e1*t1+e2*t2+e3*t3+e4*t4+e5*t5)/e0 := by
  apply (mul_right_cancel₀ he)
  rw [div_mul_cancel₀ _ he]
  have h : t0*e0+(e1*t1+e2*t2+e3*t3+e4*t4+e5*t5)=0 := by
    calc
      _ = e0*t0+e1*t1+e2*t2+e3*t3+e4*t4+e5*t5 := by ring
      _ = 0 := ht
  exact eq_neg_of_add_eq_zero_left h

#print axioms certificate_lift
#print axioms affine_repair
#print axioms evaluation_covector
#print axioms pivot_exists
#print axioms solve_pivot
end AspisR19.H1RelationLift
