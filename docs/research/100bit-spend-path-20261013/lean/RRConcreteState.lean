import RRFiniteRootSamplerNormalizedStateBridge
import RRSubstitutionOuterDegreeBound

namespace AspisR1.RRConcreteState
open CompPoly
open AspisR1.RRFiniteRootSamplerNormalizedStateBridge

/-- Runtime coefficient rows and the last inner-X slice included in the
parent model. Polynomial interpretations and invariants are proof-only. -/
structure RawState (K : Type) where
  rows : List (List K)
  maxX : Nat

variable {K : Type} [Field K] [BEq K] [LawfulBEq K]

def scalarPolynomial (s : RawState K) : CPolynomial K :=
  CPolynomial.ofArray ((s.rows[0]?).getD []).toArray

/-- Coefficients of Q(X,0), formed directly from the stored first entries. -/
def zeroColumnPolynomial (s : RawState K) : CPolynomial K :=
  CPolynomial.ofArray (List.ofFn fun i : Fin (s.maxX+1) =>
    RRDenseCoeffVector.coeffAt ((s.rows[i.val]?).getD []) 0).toArray

def zeroTest (s : RawState K) : Bool := zeroColumnPolynomial s == 0

/-- One deterministic normalization step after a returned scalar root.
The finite scan is explicit and any unexpected failure remains an abort. -/
def normalizeChild? [DecidableEq K] (ell : Nat) (s : RawState K) (a : K) :
    Option (RawState K) :=
  match RRFiniteCoeffScannerV9.firstNonzeroFullRows
    (RRVectorActualScanner.rowsUpTo s.rows a s.maxX ell) with
  | none => none
  | some (v,_) => some ⟨normalizedRuntimeState s.rows a s.maxX ell v,
      s.maxX+ell-v⟩

noncomputable section
open Polynomial RRVectorRowPolynomialBridge RRVectorNormalizedRows
open RRRootDescent RRActualBivariateTaylorBridge

def model (s : RawState K) : (K[X])[X] := actualParent s.rows s.maxX

def Valid (ell : Nat) (s : RawState K) : Prop :=
  inputPolynomial s.rows 0 ≠ 0 ∧
    ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell

theorem scalarPolynomial_toPoly (s : RawState K) :
    (scalarPolynomial s).toPoly = inputPolynomial s.rows 0 := by
  exact ofArray_toPolynomial _

theorem zeroColumn_coeff (s : RawState K) (n : Nat) :
    (zeroColumnPolynomial s).toPoly.coeff n =
      if n < s.maxX+1 then (inputPolynomial s.rows n).coeff 0 else 0 := by
  rw [zeroColumnPolynomial, ofArray_toPolynomial, RRDenseCoeffVector.coeff_toPolynomial]
  simp only [inputPolynomial, RRDenseCoeffVector.coeff_toPolynomial]
  by_cases hn : n < s.maxX+1
  · simp only [RRDenseCoeffVector.coeffAt, List.getElem?_ofFn, dif_pos hn,
      Option.getD_some, vectorAt, if_pos hn]
  · simp only [RRDenseCoeffVector.coeffAt, List.getElem?_ofFn, dif_neg hn,
      Option.getD_none, if_neg hn]

#print axioms scalarPolynomial
#print axioms zeroColumnPolynomial
#print axioms zeroTest
#print axioms normalizeChild?
#print axioms scalarPolynomial_toPoly
#print axioms zeroColumn_coeff
end
end AspisR1.RRConcreteState
