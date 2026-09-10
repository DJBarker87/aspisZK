import QuadraticSpecializationGuarded
import QuadraticSpecializationOdd

/-!
Total finite root-event accounting for one fixed unscaled discriminant
decomposition. H-specialization zeros are charged through the literal
leading-X coefficient of H, not an assumed exception bound.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticSpecializationTotal
noncomputable section
open Polynomial

/-- The actual leading coefficient supplies a fixed scalar obstruction to
identically zero specialization. No degree-preservation assumption is used. -/
theorem zero_specialization_forces_fixed_root
    {K : Type*} [Field K] (H : Polynomial K[X]) (gamma : K)
    (zero : H.map (Polynomial.evalRingHom gamma) = 0) :
    H.leadingCoeff.eval gamma = 0 := by
  have coefficient := congrArg (fun p : K[X] => p.coeff H.natDegree) zero
  rw [Polynomial.coeff_map, Polynomial.coeff_zero] at coefficient
  change (Polynomial.evalRingHom gamma) H.leadingCoeff = 0 at coefficient
  simpa only [Polynomial.coe_evalRingHom] using coefficient

/-- The H-zero class has a derived fixed-polynomial bound. Nonzeroness of
H guarantees a nonzero leading coefficient; its degree is one of the
literal coefficient-degree premises. -/
theorem zero_specializations_card_le
    {K : Type*} [Field K] [DecidableEq K]
    (H : Polynomial K[X]) (nonzero : H ≠ 0) (delta : Nat)
    (coefficients : ∀ i, (H.coeff i).natDegree ≤ delta) (G : Finset K) :
    (G.filter fun gamma => H.map (Polynomial.evalRingHom gamma) = 0).card ≤ delta := by
  have leadingNonzero : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr nonzero
  have bound : (G.filter fun gamma => H.map (Polynomial.evalRingHom gamma) = 0).card ≤
      H.leadingCoeff.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro gamma member
    exact (Polynomial.mem_roots leadingNonzero).mpr
      (zero_specialization_forces_fixed_root H gamma (Finset.mem_filter.mp member).2)
  exact bound.trans (coefficients H.natDegree)

/-- Total even-degree fixed-decomposition root count, including H-zero
specializations. The nonzero fixed-size resultant remains explicit; neither
H-regularity nor R-regularity is assumed of the full event G. -/
theorem total_even_roots_card_le
    {K : Type*} [Field K]
    (aF bF cF H R : Polynomial K[X]) (m hDelta rDelta : Nat)
    (positive : 0 < m) (hNonzero : H ≠ 0)
    (decomposition : bF ^ 2 - 4 * aF * cF = H ^ 2 * R)
    (degree : R.natDegree ≤ 2 * m)
    (hCoefficients : ∀ i, (H.coeff i).natDegree ≤ hDelta)
    (rCoefficients : ∀ i, (R.coeff i).natDegree ≤ rDelta)
    (resultantNonzero : R.resultant R.derivative (2 * m) (2 * m - 1) ≠ 0)
    (G : Finset K)
    (roots : ∀ gamma ∈ G, ∃ U : K[X],
      aF.map (Polynomial.evalRingHom gamma) * U ^ 2 +
        bF.map (Polynomial.evalRingHom gamma) * U +
          cF.map (Polynomial.evalRingHom gamma) = 0) :
    G.card ≤ hDelta + 4 * rDelta := by
  classical
  let good := G.filter fun gamma => H.map (Polynomial.evalRingHom gamma) ≠ 0
  have scaledDecomposition :
      bF ^ 2 - 4 * aF * cF = Polynomial.C (1 : K[X]) * H ^ 2 * R := by
    simpa only [Polynomial.C_1, one_mul] using decomposition
  have goodBound : good.card ≤ 4 * rDelta :=
    QuadraticSpecializationGuarded.guarded_quadratic_roots_card_le
      aF bF cF H R (1 : K[X]) m rDelta positive scaledDecomposition degree
      rCoefficients resultantNonzero good
      (fun gamma member => ⟨by simpa only [Polynomial.eval_one] using (one_ne_zero : (1 : K) ≠ 0),
        (Finset.mem_filter.mp member).2⟩)
      (fun gamma member => roots gamma (Finset.mem_filter.mp member).1)
  have badBound := zero_specializations_card_le H hNonzero hDelta hCoefficients G
  have partition := Finset.card_filter_add_card_filter_not (s := G)
    (fun gamma => H.map (Polynomial.evalRingHom gamma) = 0)
  change (G.filter fun gamma => H.map (Polynomial.evalRingHom gamma) = 0).card +
    good.card = G.card at partition
  omega

/-- Total odd-degree fixed-decomposition count, with the H-zero class and
the actual leading-R obstruction charged by their respective degrees.
Adaptive U witnesses and every H-zero branch are retained. -/
theorem total_odd_roots_card_le
    {K : Type*} [Field K]
    (aF bF cF H R : Polynomial K[X]) (hDelta rDelta : Nat)
    (hNonzero : H ≠ 0) (odd : Odd R.natDegree)
    (decomposition : bF ^ 2 - 4 * aF * cF = H ^ 2 * R)
    (hCoefficients : ∀ i, (H.coeff i).natDegree ≤ hDelta)
    (rCoefficients : ∀ i, (R.coeff i).natDegree ≤ rDelta)
    (G : Finset K)
    (roots : ∀ gamma ∈ G, ∃ U : K[X],
      aF.map (Polynomial.evalRingHom gamma) * U ^ 2 +
        bF.map (Polynomial.evalRingHom gamma) * U +
          cF.map (Polynomial.evalRingHom gamma) = 0) :
    G.card ≤ hDelta + rDelta := by
  classical
  let good := G.filter fun gamma => H.map (Polynomial.evalRingHom gamma) ≠ 0
  have goodBound : good.card ≤ rDelta :=
    QuadraticSpecializationOdd.guarded_odd_roots_card_le
      aF bF cF H R odd decomposition rDelta rCoefficients good
      (fun gamma member => (Finset.mem_filter.mp member).2)
      (fun gamma member => roots gamma (Finset.mem_filter.mp member).1)
  have badBound := zero_specializations_card_le H hNonzero hDelta hCoefficients G
  have partition := Finset.card_filter_add_card_filter_not (s := G)
    (fun gamma => H.map (Polynomial.evalRingHom gamma) = 0)
  change (G.filter fun gamma => H.map (Polynomial.evalRingHom gamma) = 0).card +
    good.card = G.card at partition
  omega

#print axioms zero_specialization_forces_fixed_root
#print axioms zero_specializations_card_le
#print axioms total_even_roots_card_le
#print axioms total_odd_roots_card_le

end
end AspisV8.QuadraticSpecializationTotal
