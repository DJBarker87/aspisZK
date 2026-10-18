import RRActualNormalizedTransition
import RRVectorActualScannerV2

open Polynomial
noncomputable section
namespace RRRootDescent
variable {K : Type*} [Field K] [DecidableEq K]
open RRActualBivariateTaylorBridge RRVectorRowPolynomialBridge RRVectorActualScanner

/-- The executed finite row scanner supplies the normalization index.
Its actual output gives a nonzero normalized specialization, the multiplicity
degree bound, and preservation of every candidate root. -/
theorem scanned_normalized_transition
    (gs : List (List K)) (p : K[X]) (M L : Nat) (a : K)
    (hp : p ≠ 0) (hzero : inputPolynomial gs 0 = p)
    (hL : p.rootMultiplicity a ≤ L) :
    ∃ v, v ≤ p.rootMultiplicity a ∧
      RRFiniteCoeffScannerV9.firstNonzeroFullRows (rowsUpTo gs a M L) =
        some (v, row gs a M v) ∧
      let Q := parentFromSlices (inputPolynomial gs) M
      let child := stripInnerPower (Q.comp (affine a)) v
      child.map (Polynomial.evalRingHom (0 : K)) ≠ 0 ∧
      (child.map (Polynomial.evalRingHom (0 : K))).natDegree ≤ p.rootMultiplicity a ∧
      ∀ f : K[X], child.eval f = 0 ↔ Q.eval (C a + X * f) = 0 := by
  obtain ⟨v, hv, hscan, hne, hlow⟩ :=
    actual_row_scanner_finds_first_slice gs a M L p hp hzero hL
  let Q := parentFromSlices (inputPolynomial gs) M
  have hcomp : Q.comp (affine a) = fixedParentSlice (inputPolynomial gs) a M :=
    parentFromSlices_comp _ M a
  have hlow' : ∀ k < v, xCoeffSlice (Q.comp (affine a)) k = 0 := by
    intro k hk
    rw [hcomp]
    exact hlow k hk
  have hne' : xCoeffSlice (Q.comp (affine a)) v ≠ 0 := by
    rw [hcomp]
    exact hne
  obtain ⟨hspec, hnonzero, hroots⟩ := actual_normalized_child_properties Q a v hlow' hne'
  refine ⟨v, hv, hscan, hnonzero, ?_, hroots⟩
  rw [hspec, hcomp, xCoeffSlice_fixedParent_eq_childCoeff]
  exact (RRChildSliceTaylor.childCoeff_natDegree_le _ _ _).trans hv

#print axioms scanned_normalized_transition
end RRRootDescent
