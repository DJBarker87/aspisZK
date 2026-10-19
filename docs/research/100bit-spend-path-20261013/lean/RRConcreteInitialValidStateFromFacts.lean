import RRConcreteInitialNormalizationFromFacts
import RRConcreteValidState

open Polynomial
set_option autoImplicit false
namespace AspisR1.RRConcreteInitialValidStateFromFacts

open AspisR1.RRConcreteState
open AspisR1.RRConcreteValidState
open AspisR1.RRConcreteInitialNormalizationFromFacts
open RRFiniteCoeffScannerV9
open RRVectorRowPolynomialBridge

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

def initialNormalizeTotal (s : RawState K) : RawState K :=
  match firstNonzeroFullRows (s.rows.take (s.maxX + 1)) with
  | none => s
  | some (v, _) => ⟨s.rows.drop v, s.maxX - v⟩

theorem initialNormalizeTotal_valid_roots
    (ell : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0) :
    Valid ell (initialNormalizeTotal s) ∧
      ∀ f : K[X], (model (initialNormalizeTotal s)).eval f = 0 ↔ (model s).eval f = 0 := by
  obtain ⟨v, row, childRaw, hscan, hnormalize, hraw, hvalid, hfactor, hroots⟩ :=
    initial_scan_and_normalize ell s hdegree hQ
  have htotal : initialNormalizeTotal s = childRaw := by
    unfold initialNormalizeTotal
    rw [hscan]
    simpa [hraw]
  constructor
  · rw [htotal]
    exact hvalid
  · intro f
    rw [htotal]
    exact hroots f

def initialValidState
    (ell : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0) : ValidState ell K :=
  ⟨initialNormalizeTotal s, (initialNormalizeTotal_valid_roots ell s hdegree hQ).1⟩

@[simp] theorem initialValidState_val
    (ell : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0) : (initialValidState ell s hdegree hQ).val = initialNormalizeTotal s := rfl

theorem initialValidState_roots
    (ell : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0) :
    ∀ f : K[X], (model (initialValidState ell s hdegree hQ).val).eval f = 0 ↔ (model s).eval f = 0 := by
  simpa using (initialNormalizeTotal_valid_roots ell s hdegree hQ).2

#print axioms initialNormalizeTotal
#print axioms initialNormalizeTotal_valid_roots
#print axioms initialValidState
#print axioms initialValidState_roots
end AspisR1.RRConcreteInitialValidStateFromFacts
