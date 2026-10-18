import Mathlib.Algebra.Polynomial.Taylor
import RRActualTaylorSubstitutionV3

open Polynomial
noncomputable section
namespace RRActualBivariateTaylorBridge
variable {K : Type*} [CommSemiring K]

abbrev Bivariate (K : Type*) [CommSemiring K] := Polynomial (Polynomial K)

def liftCoeffPolynomial (p : K[X]) : Bivariate K :=
  Polynomial.map (C : K →+* Polynomial K) p

def substituteByChild (p : K[X]) (a : K) : Bivariate K :=
  (liftCoeffPolynomial p).comp (C (C a) + X * C X)

theorem lift_taylor_substitution (p : K[X]) (a : K) :
    substituteByChild p a =
      (Polynomial.map (C : K →+* Polynomial K) (Polynomial.taylor a p)).comp
        (X * C X) := by
  have hsub := RRActualTaylorSubstitution.actual_affine_substitution_eq_taylor_comp
    (K := Polynomial K) (p := liftCoeffPolynomial p) (a := C a)
    (z := C X)
  have hTaylor :
      Polynomial.taylor (C a) (liftCoeffPolynomial p) =
        Polynomial.map (C : K →+* Polynomial K) (Polynomial.taylor a p) := by
    unfold liftCoeffPolynomial
    rw [Polynomial.taylor_apply, Polynomial.taylor_apply]
    rw [Polynomial.map_comp]
    simp
  unfold substituteByChild
  rw [hsub, hTaylor]

#print axioms lift_taylor_substitution
end RRActualBivariateTaylorBridge
