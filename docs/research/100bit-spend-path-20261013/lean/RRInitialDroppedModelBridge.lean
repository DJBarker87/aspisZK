import RRConcreteStatePolynomialView
import RRChildNormalization

open Polynomial
namespace AspisR1.RRInitialDroppedModelBridge

open RRVectorRowPolynomialBridge
open AspisR1.RRConcreteState
open AspisR1.RRConcreteStatePolynomialView
open RRActualBivariateTaylorBridge RRRootDescent RRVectorNormalizedRows

variable {K : Type} [Field K] [BEq K] [LawfulBEq K]

private theorem inputPolynomial_drop
    (gs : List (List K)) (v i : Nat) :
    RRVectorRowPolynomialBridge.inputPolynomial (gs.drop v) i =
      RRVectorRowPolynomialBridge.inputPolynomial gs (v+i) := by
  simp [RRVectorRowPolynomialBridge.inputPolynomial,
    RRVectorRowPolynomialBridge.vectorAt, List.getElem?_drop]

private theorem initial_strip_low_coefficients
    (s : RawState K) (v : Nat) (hv : v ≤ s.maxX)
    (hlow : ∀ i < v, inputPolynomial s.rows i = 0) :
    ∀ j n, n < v → ((model s).coeff j).coeff n = 0 := by
  intro j n hn
  have hslice : xCoeffSlice (model s) n = 0 := by
    have hread := parent_inner_slice (inputPolynomial s.rows) s.maxX n
    have hnM : n ≤ s.maxX := by omega
    simpa only [model, actualParent, hnM, ↓reduceIte, hlow n hn] using hread
  have hc := congrArg (fun p : K[X] => p.coeff j) hslice
  simpa [xCoeffSlice_coeff] using hc

theorem dropped_model_eq_stripInnerPower
    (s : RawState K) (v : Nat) (hv : v ≤ s.maxX)
    (hlow : ∀ i < v, inputPolynomial s.rows i = 0) :
    model ⟨s.rows.drop v, s.maxX-v⟩ =
      RRRootDescent.stripInnerPower (model s) v := by
  let child : RawState K := ⟨s.rows.drop v, s.maxX-v⟩
  have hlowc := initial_strip_low_coefficients s v hv hlow
  have hstrip (n : Nat) :
      xCoeffSlice (RRRootDescent.stripInnerPower (model s) v) n =
        xCoeffSlice (model s) (v+n) := by
    apply Polynomial.ext
    intro j
    rw [xCoeffSlice_coeff, xCoeffSlice_coeff]
    exact RRRootDescent.stripInnerPower_coeff_readback (model s) v j n hlowc
  have hslices : ∀ n, xCoeffSlice (model child) n =
      xCoeffSlice (RRRootDescent.stripInnerPower (model s) v) n := by
    intro n
    by_cases hn : n ≤ s.maxX-v
    · have hvn : v+n ≤ s.maxX := by omega
      have hleft := parent_inner_slice (inputPolynomial child.rows) child.maxX n
      have hleft' : xCoeffSlice (model child) n =
          if n ≤ child.maxX then inputPolynomial child.rows n else 0 := by
        simpa only [model, actualParent] using hleft
      have hright := parent_inner_slice (inputPolynomial s.rows) s.maxX (v+n)
      have hright' : xCoeffSlice (model s) (v+n) =
          if v+n ≤ s.maxX then inputPolynomial s.rows (v+n) else 0 := by
        simpa only [model, actualParent] using hright
      rw [hleft', if_pos hn, hstrip, hright', if_pos hvn]
      simp [child, inputPolynomial_drop]
    · have hvn : s.maxX < v+n := by omega
      have hnot : ¬ (v+n ≤ s.maxX) := by omega
      have hleft := parent_inner_slice (inputPolynomial child.rows) child.maxX n
      have hleft' : xCoeffSlice (model child) n =
          if n ≤ child.maxX then inputPolynomial child.rows n else 0 := by
        simpa only [model, actualParent] using hleft
      have hright := parent_inner_slice (inputPolynomial s.rows) s.maxX (v+n)
      have hright' : xCoeffSlice (model s) (v+n) =
          if v+n ≤ s.maxX then inputPolynomial s.rows (v+n) else 0 := by
        simpa only [model, actualParent] using hright
      rw [hleft', if_neg hn, hstrip, hright', if_neg hnot]
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro n
  have hc := congrArg (fun p : K[X] => p.coeff j) (hslices n)
  simpa [xCoeffSlice_coeff] using hc

#print axioms dropped_model_eq_stripInnerPower
end AspisR1.RRInitialDroppedModelBridge
