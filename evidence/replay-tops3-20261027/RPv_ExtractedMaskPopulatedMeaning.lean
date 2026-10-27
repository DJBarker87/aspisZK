import ExtractedMaskCallerModel
import RPv_ExtractedMaskCoefficientLoopMeaning
import RPv_ExtractedMaskCoefficientScheduledSum

/-! Interpretation of both completed population loops as the disjoint source
coefficient schedules, and composition with the actual mask caller. This uses
the local exact QM31 formulas. Transport to the historical WideExact semantic
relation through its field embedding remains a separate obligation. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskPopulatedMeaning

open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskCoefficientArray
open AspisR1.ExtractedMaskCoefficientSchedule
open AspisR1.ExtractedMaskCallerModel
open AspisR1.ExtractedMaskCoefficientLoopMeaning
  (c1Meaning maskMeaning loop0_model_interval loop1_model_interval)

abbrev coeff := AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients
abbrev exceptionIndex := AspisR1.ExtractedMaskCoefficientScheduledSum.exceptionIndex

theorem initial_coefficient_zero (e : Fin 27) :
    coeff initialCoefficients e = 0 := by
  simp only [coeff, AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients,
    AspisR1.ExtractedMaskCoefficientStep.coefficientCell,
    initialCoefficients, Array.repeat_val, List.getElem_replicate]
  exact AspisR1.ExtractedMaskConstants.zero_decode

/-- The completed arrays contain each transformed input at its exact
scheduled coefficient, and the only unfilled coefficient remains zero. -/
theorem populated_coefficients_meaning
    (c1 : C1) (maskOnly : MaskOnly)
    (hc1 : ∀ j : Fin 16, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j))
    (hmask : ∀ j : Fin 10, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j)) :
    (∀ j : Fin 16, coeff (populatedCoefficients c1 maskOnly) (c1Exponent j) =
      c1Meaning c1 j) ∧
    (∀ j : Fin 10, coeff (populatedCoefficients c1 maskOnly) (maskExponent j) =
      maskMeaning maskOnly j) ∧
    coeff (populatedCoefficients c1 maskOnly) exceptionIndex = 0 := by
  let after0 := AspisR1.ExtractedMaskCoefficientLoop0.writeModel0
    c1 initialCoefficients range0 16
  have h0 := loop0_model_interval c1 initialCoefficients range0 16
    (by simp [range0, state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS])
    (by simp [range0, state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS]) hc1
  have h1 := loop1_model_interval maskOnly after0 range1 10
    (by simp [range1, state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS])
    (by simp [range1, state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS]) hmask
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hpreserve := h1.2 (c1Exponent j) (by
      intro k _ _
      exact (schedules_disjoint j k).symm)
    have hvalue := h0.1 j (by change 0 ≤ j.val; omega) j.isLt
    exact hpreserve.trans hvalue
  · intro j
    exact h1.1 j (by change 0 ≤ j.val; omega) j.isLt
  · have hnoC1 : ∀ j : Fin 16, c1Exponent j ≠ exceptionIndex := by
      intro j heq
      have hne := (schedules_cover_except_23 exceptionIndex).mp
        (Or.inl ⟨j, heq⟩)
      exact hne rfl
    have hnoMask : ∀ j : Fin 10, maskExponent j ≠ exceptionIndex := by
      intro j heq
      have hne := (schedules_cover_except_23 exceptionIndex).mp
        (Or.inr ⟨j, heq⟩)
      exact hne rfl
    have hp1 := h1.2 exceptionIndex (by intro j _ _; exact hnoMask j)
    have hp0 := h0.2 exceptionIndex (by intro j _ _; exact hnoC1 j)
    exact hp1.trans (hp0.trans (initial_coefficient_zero exceptionIndex))

/-- The Horner polynomial's bounded Nat sum is the same finite coefficient
evaluation used by the schedule-reindexing theorem. -/
theorem coefficientPolynomial_eq_fin_sum (a : Coefficients) (x : ExactQM) :
    AspisR1.ExtractedMaskHornerPolynomial.coefficientPolynomial
      (AspisR1.ExtractedMaskHornerCaller.coefficientValue a) x =
      ∑ e : Fin 27, coeff a e * x ^ e.val := by
  unfold AspisR1.ExtractedMaskHornerPolynomial.coefficientPolynomial
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro e _
  simp [AspisR1.ExtractedMaskHornerCaller.coefficientValue, e.isLt,
    coeff, AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients,
    AspisR1.ExtractedMaskCoefficientStep.coefficientCell,
    AspisR1.ExtractedMaskHornerCaller.decode]

private theorem scheduled_sum_of_meaning
    (a : Coefficients) (c1 : C1) (maskOnly : MaskOnly) (x : ExactQM)
    (h0 : ∀ j : Fin 16, coeff a (c1Exponent j) = c1Meaning c1 j)
    (h1 : ∀ j : Fin 10, coeff a (maskExponent j) = maskMeaning maskOnly j)
    (hzero : coeff a exceptionIndex = 0) :
    (∑ e : Fin 27, coeff a e * x ^ e.val) =
      (∑ j : Fin 16, c1Meaning c1 j * x ^ (c1Exponent j).val) +
        ∑ j : Fin 10, maskMeaning maskOnly j * x ^ (maskExponent j).val := by
  classical
  let term : Fin 27 → ExactQM := fun e => coeff a e * x ^ e.val
  calc
    (∑ e : Fin 27, coeff a e * x ^ e.val) =
        ∑ d : AspisR1.ExtractedMaskCoefficientScheduledSum.ScheduleIndex.{0},
          term (AspisR1.ExtractedMaskCoefficientScheduledSum.scheduleIndex d) := by
      simpa [term, AspisR1.ExtractedMaskCoefficientScheduledSum.scheduleEquiv] using
        (Equiv.sum_comp
          AspisR1.ExtractedMaskCoefficientScheduledSum.scheduleEquiv term).symm
    _ =
        (∑ j : Fin 16, c1Meaning c1 j * x ^ (c1Exponent j).val) +
          ∑ j : Fin 10, maskMeaning maskOnly j * x ^ (maskExponent j).val := by
      simp [term, AspisR1.ExtractedMaskCoefficientScheduledSum.scheduleIndex,
        h0, h1, hzero]

def scheduledPolynomial (c1 : C1) (maskOnly : MaskOnly) (x : ExactQM) : ExactQM :=
  (∑ j : Fin 16, c1Meaning c1 j * x ^ (c1Exponent j).val) +
    ∑ j : Fin 10, maskMeaning maskOnly j * x ^ (maskExponent j).val

private theorem scheduledPolynomial_eq (c1 : C1) (maskOnly : MaskOnly)
    (x : ExactQM) :
    scheduledPolynomial c1 maskOnly x =
      (∑ j : Fin 16, c1Meaning c1 j * x ^ (c1Exponent j).val) +
        ∑ j : Fin 10, maskMeaning maskOnly j * x ^ (maskExponent j).val := rfl

-- Keep the finite schedule symbolic during elaboration; its defining equation
-- is used explicitly below when applying the reindexing theorem.
attribute [local irreducible] scheduledPolynomial

theorem populatedPolynomial_eq_scheduled
    (c1 : C1) (maskOnly : MaskOnly) (x : ExactQM)
    (hc1 : ∀ j : Fin 16, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j))
    (hmask : ∀ j : Fin 10, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j)) :
    AspisR1.ExtractedMaskHornerPolynomial.coefficientPolynomial
      (AspisR1.ExtractedMaskHornerCaller.coefficientValue
        (populatedCoefficients c1 maskOnly)) x =
      scheduledPolynomial c1 maskOnly x := by
  obtain ⟨h0, h1, hzero⟩ := populated_coefficients_meaning c1 maskOnly hc1 hmask
  rw [coefficientPolynomial_eq_fin_sum]
  rw [scheduledPolynomial_eq]
  exact scheduled_sum_of_meaning (populatedCoefficients c1 maskOnly)
    c1 maskOnly x h0 h1 hzero

/-- Full extracted mask computation equals the local exact scheduled formula.
The premises are solely canonicality of the source inputs; all array writes,
call successes and intermediate canonicality are discharged by composition. -/
theorem current_selected_mask_value_scheduled
    (c1 : C1) (maskOnly : MaskOnly) (g : QM) (point : Array QM 10#usize)
    (hc1 : ∀ j : Fin 16, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j))
    (hmask : ∀ j : Fin 10, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j))
    (hpoint : ∀ i : Nat, ∀ hi : i < 10, CanonicalQM
      (AspisR1.ExtractedMaskLinearLoop.pointAtNat point i hi))
    (hg : CanonicalQM g) :
    ∃ out : QM,
      state_only_hiding.state_only_selected_mask_value c1 maskOnly g point = .ok out ∧
      CanonicalQM out ∧
      decode out =
        scheduledPolynomial c1 maskOnly
          (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
            (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) +
        (1 + (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
          (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) ^ 26) * decode g := by
  obtain ⟨out, hrun, hcanonical, hvalue⟩ :=
    selected_mask_value_populated_model c1 maskOnly g point hc1 hmask hpoint hg
  refine ⟨out, hrun, hcanonical, ?_⟩
  rw [populatedPolynomial_eq_scheduled c1 maskOnly _ hc1 hmask] at hvalue
  exact hvalue

#print axioms initial_coefficient_zero
#print axioms populated_coefficients_meaning
#print axioms coefficientPolynomial_eq_fin_sum
#print axioms populatedPolynomial_eq_scheduled
#print axioms current_selected_mask_value_scheduled

end AspisR1.ExtractedMaskPopulatedMeaning
