import RRConcreteStatePolynomialView
import CompPoly.Bivariate.ToPoly

set_option autoImplicit false

open Polynomial CompPoly

namespace AspisR1.GSRawStateCoefficientBridge

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

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

/-- A weighted-degree certificate bounds the finite coefficient rectangle.
The explicit `hwindow` premise records the chosen max-Y row; it is discharged
by the interpolation parameters (for example when `maxY = floor(D/d)`). -/
theorem coefficient_window_of_weightedDegree
    (Q : CBivariate K) (d D maxY : Nat)
    (hdegree : Q.natWeightedDegree 1 d ≤ D)
    (hwindow : D < d * (maxY + 1)) :
    (∀ i j, D < i → CBivariate.coeff Q i j = 0) ∧
    (∀ i j, maxY < j → CBivariate.coeff Q i j = 0) := by
  have hcoeff : ∀ i j, CBivariate.coeff Q i j ≠ 0 → i + d * j ≤ D := by
    intro i j hne
    simpa using ((CBivariate.natWeightedDegree_le_iff_coeff Q 1 d D).mp
      hdegree i j hne)
  constructor
  · intro i j hi
    by_contra hzero
    have hle := hcoeff i j hzero
    omega
  · intro i j hj
    by_contra hzero
    have hle := hcoeff i j hzero
    have hmul : d * (maxY + 1) ≤ d * j :=
      Nat.mul_le_mul_left d (by omega)
    have hgt : D < d * j := lt_of_lt_of_le hwindow hmul
    omega

theorem gsState_model_eq_of_weightedDegree
    (Q : CBivariate K) (D maxY d : Nat)
    (hdegree : Q.natWeightedDegree 1 d ≤ D)
    (hwindow : D < d * (maxY + 1)) :
    AspisR1.RRConcreteState.model (gsState Q D maxY) = CBivariate.toPoly Q := by
  obtain ⟨hX, hY⟩ := coefficient_window_of_weightedDegree Q d D maxY hdegree hwindow
  exact gsState_model_eq Q D maxY hY hX

theorem toPoly_ne_zero_of_ne_zero (Q : CBivariate K) (hQ : Q ≠ 0) :
    CBivariate.toPoly Q ≠ 0 := by
  intro hpoly
  apply hQ
  apply CBivariate.eq_iff_coeff.mpr
  intro i j
  have hcoeff := congrArg (fun p : (K[X])[X] => (p.coeff j).coeff i) hpoly
  rw [CBivariate.coeff_toPoly] at hcoeff
  exact hcoeff

/-- Full raw constructor contract for GS output: weighted degree plus the
chosen row window yields exact model reconstruction and row degree bounds.
Nonzero GS output stays nonzero in the polynomial model. -/
theorem gsState_contract
    (Q : CBivariate K) (D maxY d : Nat)
    (hdegree : Q.natWeightedDegree 1 d ≤ D)
    (hwindow : D < d * (maxY + 1)) :
    AspisR1.RRConcreteState.model (gsState Q D maxY) = CBivariate.toPoly Q ∧
    (∀ i ≤ D,
      (RRVectorRowPolynomialBridge.inputPolynomial (gsRows Q D maxY) i).natDegree ≤ maxY) ∧
    (Q ≠ 0 → AspisR1.RRConcreteState.model (gsState Q D maxY) ≠ 0) := by
  obtain ⟨hX, hY⟩ := coefficient_window_of_weightedDegree Q d D maxY hdegree hwindow
  have hmodel := gsState_model_eq Q D maxY hY hX
  refine ⟨hmodel, ?_, ?_⟩
  · intro i hi
    rw [inputPolynomial_eq_slice Q D maxY i (hY i) hi]
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [RRActualBivariateTaylorBridge.xCoeffSlice_coeff, CBivariate.coeff_toPoly]
    exact hY i j hj
  · intro hQ
    rw [hmodel]
    exact toPoly_ne_zero_of_ne_zero Q hQ

#print axioms coefficient_window_of_weightedDegree
#print axioms gsState_model_eq_of_weightedDegree
#print axioms toPoly_ne_zero_of_ne_zero
#print axioms gsState_contract

end AspisR1.GSRawStateCoefficientBridge
