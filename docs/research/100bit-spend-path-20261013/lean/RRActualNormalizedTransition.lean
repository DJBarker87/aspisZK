import RRNormalizedChildSlice

open Polynomial
noncomputable section
namespace RRRootDescent
variable {K : Type*} [Field K]
open RRActualBivariateTaylorBridge

/-- A fixed parent presented by its inner-X coefficient polynomials. -/
def parentFromSlices (g : Nat → K[X]) (M : Nat) : (K[X])[X] :=
  ∑ i ∈ Finset.range (M + 1), C ((X : K[X]) ^ i) * liftCoeffPolynomial (g i)

theorem parentFromSlices_comp (g : Nat → K[X]) (M : Nat) (a : K) :
    (parentFromSlices g M).comp (affine a) = fixedParentSlice g a M := by
  simp only [parentFromSlices, fixedParentSlice, substituteByChild, affine,
    Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp]

/-- One actual normalized transition simultaneously preserves roots and gives
the child-specialization degree bound used by the RR tree budget. -/
theorem exists_actual_normalized_transition
    (g : Nat → K[X]) (p : K[X]) (M : Nat) (a : K)
    (hp : p ≠ 0) (hzero : g 0 = p) :
    ∃ v, v ≤ p.rootMultiplicity a ∧
      let child := stripInnerPower ((parentFromSlices g M).comp (affine a)) v
      child.map (Polynomial.evalRingHom (0 : K)) ≠ 0 ∧
      (child.map (Polynomial.evalRingHom (0 : K))).natDegree ≤ p.rootMultiplicity a ∧
      ∀ f : K[X], child.eval f = 0 ↔ (parentFromSlices g M).eval (C a + X * f) = 0 := by
  obtain ⟨v, hv, hne, hlow, hdegree⟩ :=
    exists_actual_fixed_parent_first_nonzero_slice g a p M hp hzero
  have hcomp := parentFromSlices_comp g M a
  have hlow' : ∀ k < v, xCoeffSlice ((parentFromSlices g M).comp (affine a)) k = 0 := by
    intro k hk
    rw [hcomp]
    exact hlow k hk
  have hne' : xCoeffSlice ((parentFromSlices g M).comp (affine a)) v ≠ 0 := by
    rw [hcomp]
    exact hne
  obtain ⟨hspec, hnonzero, hroots⟩ :=
    actual_normalized_child_properties (parentFromSlices g M) a v hlow' hne'
  refine ⟨v, hv, hnonzero, ?_, hroots⟩
  rw [hspec, hcomp]
  exact hdegree

#print axioms parentFromSlices_comp
#print axioms exists_actual_normalized_transition
end RRRootDescent
