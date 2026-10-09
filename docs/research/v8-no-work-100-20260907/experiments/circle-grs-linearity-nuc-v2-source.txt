import AspisFormal.V5FriInitialCircleEncoderIdentity

/-! Polynomial-level linearity of the source circle-to-GRS transformation.
All finite sums and lift degrees are proved symbolically before specializing
512/511 or the concrete field. No stored evaluation domain is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.CircleGRSLinearity
open Polynomial
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriCircleEncoderDistance
noncomputable section
variable {K : Type*} [Field K]

theorem monomial_add {n : Nat} (u v : Fin n → K) :
    monomialPolynomial (u+v) = monomialPolynomial u + monomialPolynomial v := by
  classical
  simp only [monomialPolynomial, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib]

theorem monomial_smul {n : Nat} (a : K) (u : Fin n → K) :
    monomialPolynomial (a • u) = a • monomialPolynomial u := by
  classical
  simp only [monomialPolynomial, Pi.smul_apply, smul_eq_mul, map_mul,
    Polynomial.smul_eq_C_mul, Finset.mul_sum, mul_assoc]

theorem natural_add {n : Nat} (u v : Fin n → K) :
    naturalCoefficientPolynomial (u+v) =
      naturalCoefficientPolynomial u + naturalCoefficientPolynomial v := by
  unfold naturalCoefficientPolynomial naturalToMonomialCoefficients
  rw [Matrix.mulVec_add, monomial_add]

theorem natural_smul {n : Nat} (a : K) (u : Fin n → K) :
    naturalCoefficientPolynomial (a • u) = a • naturalCoefficientPolynomial u := by
  unfold naturalCoefficientPolynomial naturalToMonomialCoefficients
  rw [Matrix.mulVec_smul, monomial_smul]

theorem fractional_add (d : Nat) (p q : K[X]) :
    fractionalLift d (p+q) = fractionalLift d p + fractionalLift d q := by
  classical
  simp only [fractionalLift, Polynomial.coeff_add, map_add, add_mul,
    Finset.sum_add_distrib]

theorem fractional_smul (d : Nat) (a : K) (p : K[X]) :
    fractionalLift d (a • p) = a • fractionalLift d p := by
  classical
  simp only [fractionalLift, Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul,
    map_mul, Finset.mul_sum, mul_assoc]

theorem mobius_add (d : Nat) (p q : K[X]) :
    mobiusLift d (p+q) = mobiusLift d p + mobiusLift d q := by
  rw [mobiusLift, fractional_add, map_add]
  rfl

theorem mobius_smul (d : Nat) (a : K) (p : K[X]) :
    mobiusLift d (a • p) = a • mobiusLift d p := by
  rw [mobiusLift, fractional_smul, map_smul]
  rfl

theorem numerator_add (p0 p1 q0 q1 : K[X]) :
    circleNumerator (p0+q0) (p1+q1) =
      circleNumerator p0 p1 + circleNumerator q0 q1 := by
  unfold circleNumerator
  rw [mobius_add, mobius_add, mul_add]
  abel

theorem numerator_smul (a : K) (p0 p1 : K[X]) :
    circleNumerator (a • p0) (a • p1) = a • circleNumerator p0 p1 := by
  unfold circleNumerator
  rw [mobius_smul, mobius_smul, smul_add, mul_smul_comm]

theorem initial_add (u v : Fin 1024 → K) :
    initialP0 (u+v) = initialP0 u + initialP0 v ∧
    initialP1 (u+v) = initialP1 u + initialP1 v := by
  have even : evenCoefficients (n := 512) (u+v) =
      evenCoefficients u + evenCoefficients v := by funext i; rfl
  have odd : oddCoefficients (n := 512) (u+v) =
      oddCoefficients u + oddCoefficients v := by funext i; rfl
  constructor
  · unfold initialP0
    rw [even, natural_add]
  · unfold initialP1
    rw [odd, natural_add]

theorem initial_smul (a : K) (u : Fin 1024 → K) :
    initialP0 (a • u) = a • initialP0 u ∧
    initialP1 (a • u) = a • initialP1 u := by
  have even : evenCoefficients (n := 512) (a • u) =
      a • evenCoefficients u := by funext i; rfl
  have odd : oddCoefficients (n := 512) (a • u) =
      a • oddCoefficients u := by funext i; rfl
  constructor
  · unfold initialP0
    rw [even, natural_smul]
  · unfold initialP1
    rw [odd, natural_smul]

/-- Literal source polynomial, not an arbitrary bounded-degree ambient map. -/
def numeratorMessage : (Fin 1024 → K) →ₗ[K] K[X] where
  toFun u := circleNumerator (initialP0 u) (initialP1 u)
  map_add' u v := by
    rw [(initial_add u v).1, (initial_add u v).2, numerator_add]
  map_smul' a u := by
    rw [(initial_smul a u).1, (initial_smul a u).2, numerator_smul]
    rfl

#print axioms natural_add
#print axioms natural_smul
#print axioms numerator_add
#print axioms numerator_smul
#print axioms numeratorMessage
end
end AspisV8.CircleGRSLinearity
