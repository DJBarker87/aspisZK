import RRConcreteStatePolynomialView
import CompPoly.Bivariate.ToPoly

set_option autoImplicit false

open Polynomial CompPoly

namespace AspisR1.GSRawStateCoefficientBridge

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [Nontrivial K] [DecidableEq K]

/-- Store a GS polynomial's coefficient at `X^i Y^j` in runtime row `i`,
column `j`. Rows are indexed by inner-X degree, as required by RawState. -/
def gsRows (Q : CBivariate K) (maxX maxY : Nat) : List (List K) :=
  List.ofFn fun i : Fin (maxX + 1) =>
    List.ofFn fun j : Fin (maxY + 1) => CBivariate.coeff Q i.val j.val

def gsState (Q : CBivariate K) (maxX maxY : Nat) : AspisR1.RRConcreteState.RawState K :=
  ⟨gsRows Q maxX maxY, maxX⟩

/-- Each stored inner-X row decodes to the corresponding coefficient slice of
the CompPoly bivariate polynomial, provided the outer-Y window is wide enough. -/
theorem inputPolynomial_eq_slice (Q : CBivariate K) (maxX maxY i : Nat)
    (hY : ∀ j, maxY < j → CBivariate.coeff Q i j = 0) (hi : i ≤ maxX) :
    RRVectorRowPolynomialBridge.inputPolynomial (gsRows Q maxX maxY) i =
      RRActualBivariateTaylorBridge.xCoeffSlice (CBivariate.toPoly Q) i := by
  apply Polynomial.ext
  intro j
  change (RRDenseCoeffVector.toPolynomial
      (RRVectorRowPolynomialBridge.vectorAt (gsRows Q maxX maxY) i)).coeff j = _
  rw [RRDenseCoeffVector.coeff_toPolynomial]
  change RRDenseCoeffVector.coeffAt ((gsRows Q maxX maxY)[i]?.getD []) j = _
  unfold RRDenseCoeffVector.coeffAt
  have hi' : i < maxX + 1 := by omega
  by_cases hj : j < maxY + 1
  · simp only [gsRows, List.getElem?_ofFn, dif_pos hi', dif_pos hj,
      Option.getD_some]
    rw [RRActualBivariateTaylorBridge.xCoeffSlice_coeff, CBivariate.coeff_toPoly]
  · have hgt : maxY < j := by omega
    simp only [gsRows, List.getElem?_ofFn, dif_pos hi', dif_neg hj,
      Option.getD_some, Option.getD_none]
    rw [RRActualBivariateTaylorBridge.xCoeffSlice_coeff, CBivariate.coeff_toPoly]
    exact (hY j hgt).symm

/-- The executable RawState model is exactly the CompPoly polynomial, after
transposing its outer-Y-major coefficient description into inner-X rows. -/
theorem gsState_model_eq (Q : CBivariate K) (maxX maxY : Nat)
    (hY : ∀ i j, maxY < j → CBivariate.coeff Q i j = 0)
    (hX : ∀ i j, maxX < i → CBivariate.coeff Q i j = 0) :
    AspisR1.RRConcreteState.model (gsState Q maxX maxY) = CBivariate.toPoly Q := by
  have hslices (i : Nat) :
      RRActualBivariateTaylorBridge.xCoeffSlice
          (AspisR1.RRConcreteState.model (gsState Q maxX maxY)) i =
        RRActualBivariateTaylorBridge.xCoeffSlice (CBivariate.toPoly Q) i := by
    by_cases hi : i ≤ maxX
    · have hparent := AspisR1.RRConcreteStatePolynomialView.parent_inner_slice
        (RRVectorRowPolynomialBridge.inputPolynomial (gsRows Q maxX maxY)) maxX i
      calc
        RRActualBivariateTaylorBridge.xCoeffSlice
            (AspisR1.RRConcreteState.model (gsState Q maxX maxY)) i =
            RRVectorRowPolynomialBridge.inputPolynomial (gsRows Q maxX maxY) i := by
              simpa [AspisR1.RRConcreteState.model,
                RRVectorNormalizedRows.actualParent, gsState, hi] using hparent
        _ = RRActualBivariateTaylorBridge.xCoeffSlice (CBivariate.toPoly Q) i :=
              inputPolynomial_eq_slice Q maxX maxY i (hY i) hi
    · have hparent := AspisR1.RRConcreteStatePolynomialView.parent_inner_slice
        (RRVectorRowPolynomialBridge.inputPolynomial (gsRows Q maxX maxY)) maxX i
      have hmodel : RRActualBivariateTaylorBridge.xCoeffSlice
          (AspisR1.RRConcreteState.model (gsState Q maxX maxY)) i = 0 := by
        simpa [AspisR1.RRConcreteState.model,
          RRVectorNormalizedRows.actualParent, gsState, hi] using hparent
      rw [hmodel]
      apply Polynomial.ext
      intro j
      rw [RRActualBivariateTaylorBridge.xCoeffSlice_coeff,
        CBivariate.coeff_toPoly]
      exact (hX i j (by omega)).symm
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro i
  calc
    ((AspisR1.RRConcreteState.model (gsState Q maxX maxY)).coeff j).coeff i =
        (RRActualBivariateTaylorBridge.xCoeffSlice
          (AspisR1.RRConcreteState.model (gsState Q maxX maxY)) i).coeff j := by
            rw [← RRActualBivariateTaylorBridge.xCoeffSlice_coeff]
    _ = (RRActualBivariateTaylorBridge.xCoeffSlice (CBivariate.toPoly Q) i).coeff j :=
          congrArg (fun p : K[X] => p.coeff j) (hslices i)
    _ = ((CBivariate.toPoly Q).coeff j).coeff i := by
          rw [RRActualBivariateTaylorBridge.xCoeffSlice_coeff]

#print axioms inputPolynomial_eq_slice
#print axioms gsState_model_eq

end AspisR1.GSRawStateCoefficientBridge
