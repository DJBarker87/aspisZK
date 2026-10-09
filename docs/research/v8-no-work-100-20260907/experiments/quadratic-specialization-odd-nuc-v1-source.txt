import QuadraticSpecializationKernel
import QuadraticSquareCancellation
import Mathlib.Algebra.Polynomial.Roots

/-!
The actual odd-degree exception is the fixed leading-X coefficient of R,
not a supplied bad set.  D=H^2*R is a literal polynomial equality; neither
its existence nor H-specialization regularity follows from this lemma.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticSpecializationOdd
noncomputable section
open Polynomial

def leadingObstruction {K : Type*} [Field K] (R : Polynomial K[X]) : K[X] :=
  R.leadingCoeff

theorem leading_obstruction_nonzero
    {K : Type*} [Field K] (R : Polynomial K[X]) (odd : Odd R.natDegree) :
    leadingObstruction R ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro zero
  obtain ⟨k, degree⟩ := odd
  rw [zero, Polynomial.natDegree_zero] at degree
  omega

theorem leading_obstruction_degree
    {K : Type*} [Field K] (R : Polynomial K[X]) (delta : Nat)
    (coefficients : ∀ i, (R.coeff i).natDegree ≤ delta) :
    (leadingObstruction R).natDegree ≤ delta := by
  exact coefficients R.natDegree

/-- Away from the fixed leading-coefficient zero, specialization preserves
odd X degree. An actual quadratic root and nonzero H would instead force
R_gamma to be a polynomial square, contradicting that odd degree. -/
theorem actual_root_forces_leading_zero
    {K : Type*} [Field K]
    (aF bF cF H R : Polynomial K[X]) (gamma : K) (U : K[X])
    (odd : Odd R.natDegree)
    (decomposition : bF ^ 2 - 4 * aF * cF = H ^ 2 * R)
    (hNonzero : H.map (Polynomial.evalRingHom gamma) ≠ 0)
    (root : aF.map (Polynomial.evalRingHom gamma) * U ^ 2 +
      bF.map (Polynomial.evalRingHom gamma) * U +
        cF.map (Polynomial.evalRingHom gamma) = 0) :
    (leadingObstruction R).eval gamma = 0 := by
  by_contra leadingNonzero
  have leadingMapNonzero : (Polynomial.evalRingHom gamma) R.leadingCoeff ≠ 0 := by
    simpa only [Polynomial.coe_evalRingHom, leadingObstruction] using leadingNonzero
  have preserved := Polynomial.natDegree_map_of_leadingCoeff_ne_zero
    (Polynomial.evalRingHom gamma) leadingMapNonzero
  obtain ⟨k, oddDegree⟩ := odd
  have rNonzero : R.map (Polynomial.evalRingHom gamma) ≠ 0 := by
    intro zero
    rw [zero, Polynomial.natDegree_zero] at preserved
    omega
  have discriminant := QuadraticSpecializationKernel.discriminant_square_of_root
    (aF.map (Polynomial.evalRingHom gamma))
    (bF.map (Polynomial.evalRingHom gamma))
    (cF.map (Polynomial.evalRingHom gamma)) U root
  have atPoint : (bF.map (Polynomial.evalRingHom gamma)) ^ 2 -
      4 * aF.map (Polynomial.evalRingHom gamma) *
        cF.map (Polynomial.evalRingHom gamma) =
      (H.map (Polynomial.evalRingHom gamma)) ^ 2 *
        R.map (Polynomial.evalRingHom gamma) := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_ofNat] using
      congrArg (fun p : Polynomial K[X] => p.map (Polynomial.evalRingHom gamma))
        decomposition
  have squareIdentity :
      (2 * aF.map (Polynomial.evalRingHom gamma) * U +
        bF.map (Polynomial.evalRingHom gamma)) ^ 2 =
      Polynomial.C (1 : K) * (H.map (Polynomial.evalRingHom gamma)) ^ 2 *
        R.map (Polynomial.evalRingHom gamma) := by
    simpa only [Polynomial.C_1, one_mul] using discriminant.symm.trans atPoint
  obtain ⟨V, _, _, square⟩ :=
    QuadraticSquareCancellation.exists_polynomial_square_after_cancellation
      (1 : K) (H.map (Polynomial.evalRingHom gamma))
      (R.map (Polynomial.evalRingHom gamma))
      (2 * aF.map (Polynomial.evalRingHom gamma) * U +
        bF.map (Polynomial.evalRingHom gamma))
      one_ne_zero hNonzero rNonzero squareIdentity
  simp only [inv_one, Polynomial.C_1, one_mul] at square
  have evenDegree := congrArg Polynomial.natDegree square
  rw [Polynomial.natDegree_pow, preserved] at evenDegree
  omega

/-- The root set is derived from the actual pre-gamma leading coefficient,
whose nonzeroness and degree bound are established above. -/
theorem leading_exception_card_le
    {K : Type*} [Field K] [DecidableEq K] (R : Polynomial K[X]) (odd : Odd R.natDegree)
    (delta : Nat) (coefficients : ∀ i, (R.coeff i).natDegree ≤ delta)
    (Gamma : Finset K) :
    (Gamma.filter fun gamma => (leadingObstruction R).eval gamma = 0).card ≤ delta := by
  classical
  apply le_trans (b := (leadingObstruction R).natDegree)
  · apply Polynomial.card_le_degree_of_subset_roots
    intro gamma member
    exact (Polynomial.mem_roots (leading_obstruction_nonzero R odd)).mpr
      (Finset.mem_filter.mp member).2
  · exact leading_obstruction_degree R delta coefficients

/-- Exact finite counting for actual adaptive quadratic roots on the
H-regular odd branch; no resultant or leading-nonzero hypothesis is supplied.
The root witness U may be chosen separately at every gamma. -/
theorem guarded_odd_roots_card_le
    {K : Type*} [Field K]
    (aF bF cF H R : Polynomial K[X]) (odd : Odd R.natDegree)
    (decomposition : bF ^ 2 - 4 * aF * cF = H ^ 2 * R)
    (delta : Nat) (coefficients : ∀ i, (R.coeff i).natDegree ≤ delta)
    (G : Finset K)
    (regular : ∀ gamma ∈ G, H.map (Polynomial.evalRingHom gamma) ≠ 0)
    (roots : ∀ gamma ∈ G, ∃ U : K[X],
      aF.map (Polynomial.evalRingHom gamma) * U ^ 2 +
        bF.map (Polynomial.evalRingHom gamma) * U +
          cF.map (Polynomial.evalRingHom gamma) = 0) :
    G.card ≤ delta := by
  classical
  have allExceptional : G.filter (fun gamma => (leadingObstruction R).eval gamma = 0) = G := by
    apply Finset.filter_eq_self.mpr
    intro gamma member
    obtain ⟨U, root⟩ := roots gamma member
    exact actual_root_forces_leading_zero aF bF cF H R gamma U odd decomposition
      (regular gamma member) root
  have count := leading_exception_card_le R odd delta coefficients G
  rwa [allExceptional] at count

#print axioms leading_obstruction_nonzero
#print axioms leading_obstruction_degree
#print axioms actual_root_forces_leading_zero
#print axioms leading_exception_card_le
#print axioms guarded_odd_roots_card_le

end
end AspisV8.QuadraticSpecializationOdd
