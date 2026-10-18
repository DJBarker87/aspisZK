import Mathlib.Algebra.Polynomial.Taylor

open Polynomial
noncomputable section
namespace RRActualTaylorSubstitution
variable {K : Type*} [CommSemiring K]

theorem actual_affine_substitution_eq_taylor_comp
    (p : K[X]) (a : K) (z : K[X]) :
    p.comp (C a + X * z) = (Polynomial.taylor a p).comp (X * z) := by
  rw [Polynomial.taylor_apply]
  calc
    p.comp (C a + X * z) = p.comp ((X + C a).comp (X * z)) := by
      congr 1
      simp [Polynomial.add_comp, add_comm]
    _ = (p.comp (X + C a)).comp (X * z) := by
      rw [Polynomial.comp_assoc]

#print axioms actual_affine_substitution_eq_taylor_comp
end RRActualTaylorSubstitution
