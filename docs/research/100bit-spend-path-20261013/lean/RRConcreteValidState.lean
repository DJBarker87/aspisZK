import RRConcreteNormalizeChildTotal
import RRConcreteChildrenProgram
import RRConcreteStatePolynomialView
import RRBoundedSliceScannerV5

open Polynomial
namespace AspisR1.RRConcreteValidState
noncomputable section

open RRVectorActualScanner RRVectorNormalizedRows RRRootDescent
open RRActualBivariateTaylorBridge RRVectorRowPolynomialBridge
open AspisR1.RRConcreteState AspisR1.RRConcreteChildrenProgram
open AspisR1.RRConcreteNormalizeChildTotal
open AspisR1.RRConcreteStatePolynomialView

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

abbrev ValidState (ell : Nat) (K : Type) [Field K] [BEq K] [LawfulBEq K] :=
  { s : RawState K // Valid ell s }

theorem child_raw_valid (ell : Nat) (s : RawState K) (a : K)
    (hvalid : Valid ell s) : Valid ell (childRaw ell s a) := by
  obtain ⟨v, c, hv, hnormalize, hcvalid, hmodel, hroots⟩ :=
    normalizeChild_total_valid_model_roots ell s a hvalid
  have hraw : childRaw ell s a = c := by
    unfold childRaw
    rw [hnormalize]
    rfl
  simpa [hraw] using hcvalid

end
end AspisR1.RRConcreteValidState

namespace AspisR1.RRConcreteValidState
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
open AspisR1.RRConcreteState AspisR1.RRConcreteChildrenProgram

def child (ell : Nat) (s : ValidState ell K) (a : K) : ValidState ell K :=
  ⟨childRaw ell s.val a, child_raw_valid ell s.val a s.property⟩

@[simp] theorem child_val (ell : Nat) (s : ValidState ell K) (a : K) :
    (child ell s a).val = childRaw ell s.val a := rfl
end AspisR1.RRConcreteValidState

namespace AspisR1.RRConcreteValidState
noncomputable section

open RRVectorActualScanner RRVectorNormalizedRows RRRootDescent
open RRActualBivariateTaylorBridge RRVectorRowPolynomialBridge
open AspisR1.RRConcreteState AspisR1.RRConcreteChildrenProgram
open AspisR1.RRConcreteNormalizeChildTotal
open AspisR1.RRConcreteStatePolynomialView

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

theorem child_model_roots (ell : Nat) (s : ValidState ell K) (a : K) :
    ∀ f : K[X], (model (child ell s a).val).eval f = 0 ↔
      (model s.val).eval (C a + X * f) = 0 := by
  obtain ⟨v, c, hv, hnormalize, hcvalid, hmodel, hroots⟩ :=
    normalizeChild_total_valid_model_roots ell s.val a s.property
  have hraw : childRaw ell s.val a = c := by
    unfold childRaw
    rw [hnormalize]
    rfl
  intro f
  rw [child_val, hraw]
  exact hroots f

theorem child_scalar_degree_le (ell : Nat) (s : ValidState ell K) (a : K) :
    ((scalarPolynomial (child ell s a).val).toPoly).natDegree ≤
      ((scalarPolynomial s.val).toPoly).rootMultiplicity a := by
  let gs := s.val.rows
  let M := s.val.maxX
  let p := inputPolynomial gs 0
  have hp : p ≠ 0 := s.property.1
  have hdegree : ∀ j ≤ M, (inputPolynomial gs j).natDegree ≤ ell := by
    intro j hj
    exact s.property.2 j hj
  have hrootBound : p.rootMultiplicity a ≤ ell := by
    exact (RRActualSliceScanner.rootMultiplicity_le_natDegree p a hp).trans
      (hdegree 0 (Nat.zero_le _))
  obtain ⟨v, hv, hscan, hne, hlow⟩ :=
    actual_row_scanner_finds_first_slice gs a M ell p hp rfl hrootBound
  have hcomp : (actualParent gs M).comp (affine a) =
      fixedParentSlice (inputPolynomial gs) a M :=
    parentFromSlices_comp (inputPolynomial gs) M a
  have hlowChild : ∀ k < v, xCoeffSlice ((actualParent gs M).comp (affine a)) k = 0 := by
    intro k hk
    rw [hcomp]
    exact hlow k hk
  have hlowerCoeffs : ∀ j t, t < v →
      (((actualParent gs M).comp (affine a)).coeff j).coeff t = 0 :=
    lower_slices_imply_lower_coefficients ((actualParent gs M).comp (affine a)) v hlowChild
  have hscanState : normalizeChild? ell s.val a =
      some ⟨RRRuntimeNormalizedChildReconstruction.runtimeRows gs a M ell v,
        M + ell - v⟩ := by
    unfold normalizeChild?
    rw [hscan]
    rfl
  have hraw : childRaw ell s.val a =
      ⟨RRRuntimeNormalizedChildReconstruction.runtimeRows gs a M ell v,
        M + ell - v⟩ := by
    unfold childRaw
    rw [hscanState]
    rfl
  have hruntimeModel : model (child ell s a).val = actualChild gs a M v := by
    rw [child_val, hraw]
    change actualParent
      (RRRuntimeNormalizedChildReconstruction.runtimeRows gs a M ell v)
      (M + ell - v) = actualChild gs a M v
    exact RRConcreteChildModel.runtime_parent_eq_actual_child
      gs a M ell v hdegree
      (by simpa [actualParent, gs, M] using hlowerCoeffs)
      (by dsimp [M]; omega)
  have hscalarModel :
      (scalarPolynomial (child ell s a).val).toPoly =
        (model (child ell s a).val).map (Polynomial.evalRingHom (0 : K)) := by
    rw [scalarPolynomial_toPoly, model_specialization]
  have hspecializationComp :
      (actualChild gs a M v).map (Polynomial.evalRingHom (0 : K)) =
        xCoeffSlice ((actualParent gs M).comp (affine a)) v := by
    simpa [actualChild] using normalized_specialization_eq_slice
      ((actualParent gs M).comp (affine a)) v hlowChild
  have hspecialization :
      (actualChild gs a M v).map (Polynomial.evalRingHom (0 : K)) =
        fixedParentCoeffSlice (inputPolynomial gs) a M v := by
    rw [hspecializationComp, hcomp, fixedParentCoeffSlice]
  have hdegreeSlice :
      (fixedParentCoeffSlice (inputPolynomial gs) a M v).natDegree ≤
        p.rootMultiplicity a := by
    rw [fixedParentCoeffSlice, xCoeffSlice_fixedParent_eq_childCoeff]
    exact (RRChildSliceTaylor.childCoeff_natDegree_le
      (boundedInput (inputPolynomial gs) M) a v).trans hv
  have hparent : (scalarPolynomial s.val).toPoly = p := by
    simpa [p, gs] using scalarPolynomial_toPoly s.val
  rw [hparent]
  calc
    ((scalarPolynomial (child ell s a).val).toPoly).natDegree =
        ((model (child ell s a).val).map (Polynomial.evalRingHom (0 : K))).natDegree := by
          rw [hscalarModel]
    _ = (fixedParentCoeffSlice (inputPolynomial gs) a M v).natDegree := by
          rw [hruntimeModel, hspecialization]
    _ ≤ p.rootMultiplicity a := hdegreeSlice

#print axioms child
#print axioms child_raw_valid
#print axioms child_model_roots
#print axioms child_scalar_degree_le
end
end AspisR1.RRConcreteValidState
