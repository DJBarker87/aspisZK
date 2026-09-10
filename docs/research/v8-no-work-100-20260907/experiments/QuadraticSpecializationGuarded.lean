import QuadraticSpecializationSylvester
import QuadraticSquareCancellation

/-!
Guarded quadratic-root consumer of the actual Sylvester bound.
The literal discriminant decomposition is a supplied algebraic equality;
its existence, primitivity, separability and source derivation are not
asserted. The a/H specialization-zero guards remain explicit. Zero R
specializations are handled directly and degree drops need no extra charge
for this fixed-even-size nonzero-resultant theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticSpecializationGuarded
noncomputable section
open Polynomial

/-- Specialize the literal polynomial decomposition, preserving both
variable conventions: outer X and coefficient/challenge Z. -/
theorem specialize_discriminant
    {K : Type*} [Field K]
    (aF bF cF H R : Polynomial K[X]) (a : K[X]) (gamma : K)
    (decomposition : bF ^ 2 - 4 * aF * cF = Polynomial.C a * H ^ 2 * R) :
    (bF.map (Polynomial.evalRingHom gamma)) ^ 2 -
      4 * aF.map (Polynomial.evalRingHom gamma) *
        cF.map (Polynomial.evalRingHom gamma) =
      Polynomial.C (a.eval gamma) *
        (H.map (Polynomial.evalRingHom gamma)) ^ 2 *
        R.map (Polynomial.evalRingHom gamma) := by
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_ofNat, Polynomial.map_C, Polynomial.coe_evalRingHom] using
    congrArg (fun p : Polynomial K[X] => p.map (Polynomial.evalRingHom gamma))
      decomposition

/-- The actual adaptive quadratic root gives a polynomial square factor
after cancellation. No rational quotient is substituted for V, and V's
degree is derived from the fixed parity polynomial's degree allowance. -/
theorem guarded_root_gives_square
    {K : Type*} [Field K]
    (aF bF cF H R : Polynomial K[X]) (a : K[X]) (gamma : K)
    (U : K[X]) (m : Nat)
    (decomposition : bF ^ 2 - 4 * aF * cF = Polynomial.C a * H ^ 2 * R)
    (root : aF.map (Polynomial.evalRingHom gamma) * U ^ 2 +
      bF.map (Polynomial.evalRingHom gamma) * U +
        cF.map (Polynomial.evalRingHom gamma) = 0)
    (aNonzero : a.eval gamma ≠ 0)
    (hNonzero : H.map (Polynomial.evalRingHom gamma) ≠ 0)
    (rNonzero : R.map (Polynomial.evalRingHom gamma) ≠ 0)
    (degree : R.natDegree ≤ 2 * m) :
    ∃ V : K[X], V ≠ 0 ∧ V.natDegree ≤ m ∧
      R.map (Polynomial.evalRingHom gamma) = Polynomial.C ((a.eval gamma)⁻¹) * V ^ 2 := by
  have discriminant := QuadraticSpecializationKernel.discriminant_square_of_root
    (aF.map (Polynomial.evalRingHom gamma))
    (bF.map (Polynomial.evalRingHom gamma))
    (cF.map (Polynomial.evalRingHom gamma)) U root
  rw [specialize_discriminant aF bF cF H R a gamma decomposition] at discriminant
  obtain ⟨V, vNonzero, _, square⟩ :=
    QuadraticSquareCancellation.exists_polynomial_square_after_cancellation
      (a.eval gamma) (H.map (Polynomial.evalRingHom gamma))
      (R.map (Polynomial.evalRingHom gamma))
      (2 * aF.map (Polynomial.evalRingHom gamma) * U +
        bF.map (Polynomial.evalRingHom gamma))
      aNonzero hNonzero rNonzero discriminant.symm
  have mappedDegree : (R.map (Polynomial.evalRingHom gamma)).natDegree ≤ 2 * m :=
    Polynomial.natDegree_map_le.trans degree
  have vDegree := QuadraticSquareCancellation.square_factor_degree_bound
    (a.eval gamma)⁻¹ (R.map (Polynomial.evalRingHom gamma)) V m
    (inv_ne_zero aNonzero) square mappedDegree
  exact ⟨V, vNonzero, vDegree, square⟩

/-- A fixed literal decomposition and explicit a/H specialization guards
now turn actual quadratic roots into the proved 4-delta count. A zero R
specialization is the literal square 0*1^2; it is not discarded or assumed
nonzero. Degree drops are also allowed by the fixed-size Sylvester theorem.
The roots U are existential separately at each gamma and may be adaptive.
No probability, factorization existence or verifier-acceptance implication
is asserted. -/
theorem guarded_quadratic_roots_card_le
    {K : Type*} [Field K]
    (aF bF cF H R : Polynomial K[X]) (a : K[X]) (m delta : Nat)
    (positive : 0 < m)
    (decomposition : bF ^ 2 - 4 * aF * cF = Polynomial.C a * H ^ 2 * R)
    (degree : R.natDegree ≤ 2 * m)
    (coefficients : ∀ i, (R.coeff i).natDegree ≤ delta)
    (resultantNonzero : R.resultant R.derivative (2 * m) (2 * m - 1) ≠ 0)
    (G : Finset K)
    (regular : ∀ gamma ∈ G, a.eval gamma ≠ 0 ∧
      H.map (Polynomial.evalRingHom gamma) ≠ 0)
    (roots : ∀ gamma ∈ G, ∃ U : K[X],
      aF.map (Polynomial.evalRingHom gamma) * U ^ 2 +
        bF.map (Polynomial.evalRingHom gamma) * U +
          cF.map (Polynomial.evalRingHom gamma) = 0) :
    G.card ≤ 4 * delta := by
  apply QuadraticSpecializationSylvester.square_specializations_card_le
    R m delta positive coefficients resultantNonzero G
  intro gamma member
  by_cases rZero : R.map (Polynomial.evalRingHom gamma) = 0
  · refine ⟨0, 1, one_ne_zero, ?_, ?_⟩
    · simp only [Polynomial.natDegree_one]
      exact Nat.zero_le m
    · simp only [rZero, Polynomial.C_0, zero_mul]
  · obtain ⟨aNonzero, hNonzero⟩ := regular gamma member
    obtain ⟨U, root⟩ := roots gamma member
    obtain ⟨V, vNonzero, vDegree, square⟩ := guarded_root_gives_square
      aF bF cF H R a gamma U m decomposition root aNonzero hNonzero rZero degree
    exact ⟨(a.eval gamma)⁻¹, V, vNonzero, vDegree, square⟩

#print axioms specialize_discriminant
#print axioms guarded_root_gives_square
#print axioms guarded_quadratic_roots_card_le

end
end AspisV8.QuadraticSpecializationGuarded
