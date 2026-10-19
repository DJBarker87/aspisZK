import RRConcreteRawStateValidity
import RRConcreteChildModel
import RRConcreteState
import RRVectorActualScannerV2
import RRBoundedSliceScannerV5
import RRNormalizedChildSlice

open Polynomial
noncomputable section
namespace AspisR1.RRConcreteNormalizeChildTotal

open RRVectorActualScanner RRVectorNormalizedRows RRRootDescent
open RRActualBivariateTaylorBridge RRVectorRowPolynomialBridge
open AspisR1.RRConcreteState

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

/-- From a valid executable parent, the actual finite row scanner succeeds.
Its `getD` child is valid, its runtime polynomial model is the normalized
mathematical child, and every parent root is preserved by the actual step. -/
theorem normalizeChild_total_valid_model_roots
    (ell : Nat) (s : RawState K) (a : K)
    (hvalid : Valid ell s) :
    ∃ v child,
      v ≤ (inputPolynomial s.rows 0).rootMultiplicity a ∧
      normalizeChild? ell s a = some child ∧
      Valid ell child ∧
      model child = actualChild s.rows a s.maxX v ∧
      (∀ f : K[X], (model child).eval f = 0 ↔
        (model s).eval (C a + X * f) = 0) := by
  let p := inputPolynomial s.rows 0
  have hp : p ≠ 0 := hvalid.1
  have hdegree : ∀ j ≤ s.maxX, (inputPolynomial s.rows j).natDegree ≤ ell :=
    hvalid.2
  have hrootBound : p.rootMultiplicity a ≤ ell := by
    exact (RRActualSliceScanner.rootMultiplicity_le_natDegree p a hp).trans
      (hdegree 0 (Nat.zero_le _))
  have hzero : inputPolynomial s.rows 0 = p := rfl
  obtain ⟨v, hv, hscan, hne, hlow⟩ :=
    actual_row_scanner_finds_first_slice s.rows a s.maxX ell p hp hzero hrootBound
  have hvTotal : v ≤ s.maxX + ell := by omega
  have hcomp :
      (actualParent s.rows s.maxX).comp (affine a) =
        fixedParentSlice (inputPolynomial s.rows) a s.maxX :=
    parentFromSlices_comp (inputPolynomial s.rows) s.maxX a
  have hlowChild :
      ∀ k < v, xCoeffSlice
        ((actualParent s.rows s.maxX).comp (affine a)) k = 0 := by
    intro k hk
    rw [hcomp]
    exact hlow k hk
  have hneChild : xCoeffSlice
      ((actualParent s.rows s.maxX).comp (affine a)) v ≠ 0 := by
    rw [hcomp]
    exact hne
  have hlowerCoeffs : ∀ j t, t < v →
      (((actualParent s.rows s.maxX).comp (affine a)).coeff j).coeff t = 0 :=
    lower_slices_imply_lower_coefficients
      ((actualParent s.rows s.maxX).comp (affine a)) v hlowChild
  let childPoly := actualChild s.rows a s.maxX v
  have hspec : childPoly.map (Polynomial.evalRingHom (0 : K)) =
      xCoeffSlice ((actualParent s.rows s.maxX).comp (affine a)) v := by
    simpa [childPoly, actualChild] using
      normalized_specialization_eq_slice
        ((actualParent s.rows s.maxX).comp (affine a)) v hlowChild
  have hmapZero : childPoly.map (Polynomial.evalRingHom (0 : K)) =
      xCoeffSlice childPoly 0 := by
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_map, xCoeffSlice_coeff]
    change (childPoly.coeff j).eval 0 = (childPoly.coeff j).coeff 0
    rw [← Polynomial.coeff_zero_eq_eval_zero]
  have hfirst : xCoeffSlice childPoly 0 ≠ 0 := by
    rw [← hmapZero, hspec]
    exact hneChild
  let childState : RawState K :=
    ⟨RRRuntimeNormalizedChildReconstruction.runtimeRows
      s.rows a s.maxX ell v, s.maxX + ell - v⟩
  have hscanState : normalizeChild? ell s a = some childState := by
    unfold normalizeChild?
    rw [hscan]
    rfl
  have hchildValid : Valid ell childState := by
    change Valid ell ⟨
      RRRuntimeNormalizedChildReconstruction.runtimeRows s.rows a s.maxX ell v,
      s.maxX + ell - v⟩
    exact RRConcreteRawStateValidity.runtime_child_state_valid
      s.rows a s.maxX ell v hdegree
      (by simpa [actualParent] using hlowerCoeffs) hvTotal hfirst
  have hchildModel : model childState = childPoly := by
    change actualParent
      (RRRuntimeNormalizedChildReconstruction.runtimeRows s.rows a s.maxX ell v)
      (s.maxX + ell - v) = actualChild s.rows a s.maxX v
    exact RRConcreteChildModel.runtime_parent_eq_actual_child
      s.rows a s.maxX ell v hdegree
      (by simpa [actualParent] using hlowerCoeffs) hvTotal
  have hroots : ∀ f : K[X], (model childState).eval f = 0 ↔
      (model s).eval (C a + X * f) = 0 := by
    intro f
    rw [hchildModel]
    simpa [model, actualParent, childPoly, actualChild] using
      (stripInnerPower_preserves_roots
        (actualParent s.rows s.maxX) a v f hlowerCoeffs)
  exact ⟨v, childState, hv, hscanState, hchildValid, hchildModel, hroots⟩

#print axioms normalizeChild_total_valid_model_roots
end AspisR1.RRConcreteNormalizeChildTotal
