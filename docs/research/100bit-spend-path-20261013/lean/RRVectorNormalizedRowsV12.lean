import RRScannedNormalizedTransition
import RRChildNormalization
import Mathlib.Algebra.Polynomial.Eval.Coeff

open Polynomial
noncomputable section
namespace RRVectorNormalizedRows
variable {K : Type*} [Field K]
open RRVectorRowPolynomialBridge RRVectorActualScanner
open RRActualBivariateTaylorBridge RRRootDescent

/-- The bounded executable coefficient-row state for the fixed parent. -/
def rowsThrough (gs : List (List K)) (a : K) (M B : Nat) : List (List K) :=
  List.ofFn fun n : Fin (B+1) => row gs a M n.val

def polynomialRows (gs : List (List K)) (a : K) (M B : Nat) : List (K[X]) :=
  (rowsThrough gs a M B).map RRDenseCoeffVector.toPolynomial

def actualParent (gs : List (List K)) (M : Nat) : (K[X])[X] :=
  parentFromSlices (inputPolynomial gs) M

def actualChild (gs : List (List K)) (a : K) (M v : Nat) : (K[X])[X] :=
  stripInnerPower ((actualParent gs M).comp (affine a)) v

theorem polynomialRows_length (gs : List (List K)) (a : K) (M B : Nat) :
    (polynomialRows gs a M B).length = B+1 := by
  simp [polynomialRows, rowsThrough]

/-- Every retained vector row is exactly the corresponding polynomial
coefficient of the normalized child. This is the readback equation for the
runtime `drop v` normalization; the polynomial model is used only on the
right-hand side. -/
theorem normalized_row_readback
    (gs : List (List K)) (a : K) (M B v k : Nat)
    (hlower : ∀ j t, t < v →
      (((actualParent gs M).comp (affine a)).coeff j).coeff t = 0)
    (hbound : v+k ≤ B) :
    ((polynomialRows gs a M B).drop v)[k]? = some (xCoeffSlice (actualChild gs a M v) k) := by
  have hidx : v+k < B+1 := by omega
  have hrow : (polynomialRows gs a M B)[v+k]? =
      some (RRDenseCoeffVector.toPolynomial (row gs a M (v+k))) := by
    simp only [polynomialRows, List.getElem?_map, rowsThrough, List.getElem?_ofFn]
    rw [dif_pos hidx]
    rfl
  rw [List.getElem?_drop, hrow]
  apply congrArg some
  apply Polynomial.ext
  intro j
  rw [RRVectorRowPolynomialBridge.rowPolynomial_eq_parentSlice]
  rw [xCoeffSlice_coeff]
  have hcomp := parentFromSlices_comp (inputPolynomial gs) M a
  have hread := stripInnerPower_coeff_readback
    ((actualParent gs M).comp (affine a)) v j k hlower
  rw [xCoeffSlice_coeff]
  change ((fixedParentSlice (inputPolynomial gs) a M).coeff j).coeff (v+k) =
    ((stripInnerPower ((actualParent gs M).comp (affine a)) v).coeff j).coeff k
  rw [hread]
  rw [← hcomp]
  rfl
#print axioms normalized_row_readback
end RRVectorNormalizedRows
