import ExtractedMaskLinearsExact
import ExtractedMaskCoefficientLoop0
import ExtractedMaskCoefficientLoop1
import ExtractedMaskHornerCaller
import ExtractedMaskPower26
import ExtractedMaskConstants

/-! Composition of the actual extracted mask caller, including both array
population loops, Horner setup, power and final arithmetic. The result is
stated using the exact populated-array models. Its subsequent interpretation
by the two ideal coefficient schedules is a separate theorem. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskCallerModel

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Coefficients := AspisR1.ExtractedMaskCoefficientStep.Coefficients
abbrev C1 := AspisR1.ExtractedMaskCoefficientStep.C1
abbrev MaskOnly := AspisR1.ExtractedMaskCoefficientStep.MaskOnly
abbrev CanonicalQM := AspisR1.ExtractedMaskCoefficientStep.CanonicalQM
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

def initialCoefficients : Coefficients :=
  Array.repeat 27#usize field.QM31.ZERO

def range0 : core.ops.range.Range Usize :=
  { start := 0#usize, «end» := state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS }

def range1 : core.ops.range.Range Usize :=
  { start := 0#usize,
    «end» := state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS }

def populatedCoefficients (c1 : C1) (maskOnly : MaskOnly) : Coefficients :=
  AspisR1.ExtractedMaskCoefficientLoop1.writeModel1 maskOnly
    (AspisR1.ExtractedMaskCoefficientLoop0.writeModel0 c1
      initialCoefficients range0 16) range1 10

theorem initialCoefficients_canonical :
    AspisR1.ExtractedMaskCoefficientStep.CanonicalArray initialCoefficients := by
  intro i
  simpa only [initialCoefficients, Array.repeat_val, List.getElem_replicate] using
    AspisR1.ExtractedMaskConstants.zero_canonical

/-- Every source input is canonical. All intermediate success, array bounds,
array canonicality, prepared-state and literal constant facts are derived by
the component contracts. No acceptance or desired-result premise is assumed. -/
theorem selected_mask_value_populated_model
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
        AspisR1.ExtractedMaskHornerPolynomial.coefficientPolynomial
          (AspisR1.ExtractedMaskHornerCaller.coefficientValue
            (populatedCoefficients c1 maskOnly))
          (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
            (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) +
        (1 + (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
          (AspisR1.ExtractedMaskLinearsExact.decodedPoint point)) ^ 26) * decode g := by
  obtain ⟨⟨linear, explicitLinear⟩, hlinears, hlinear, hexplicit,
      hlinearValue, hexplicitValue⟩ :=
    AspisR1.ExtractedMaskLinearsExact.selected_mask_linears_exact_meaning point hpoint
  obtain ⟨coefficients1, hloop0, hcan1, hmodel0⟩ :=
    AspisR1.ExtractedMaskCoefficientLoop0.loop0_exec c1 range0
      initialCoefficients 16
      (by simp [range0, state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS])
      (by simp [range0, state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS])
      hc1 initialCoefficients_canonical
  obtain ⟨coefficients2, hloop1, hcan2, hmodel1⟩ :=
    AspisR1.ExtractedMaskCoefficientLoop1.loop1_exec maskOnly range1
      coefficients1 10
      (by simp [range1, state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS])
      (by simp [range1, state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS])
      hmask hcan1
  have hpopulated : coefficients2 = populatedCoefficients c1 maskOnly := by
    rw [hmodel1, hmodel0]
    rfl
  obtain ⟨prepared, seed, iter, shared, hprepared, hseed, hreverse,
      hhorner, hsharedCanonical, hsharedValue⟩ :=
    AspisR1.ExtractedMaskHornerCaller.prepared_seeded_horner
      coefficients2 linear hlinear hcan2
  obtain ⟨power, hpower, hpowerCanonical, hpowerValue⟩ :=
    AspisR1.ExtractedMaskPower26.current_mask_power_26 explicitLinear hexplicit
  obtain ⟨factor, hfactor, hfactorCanonical, hfactorValue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact field.QM31.ONE power
      AspisR1.ExtractedMaskConstants.one_canonical hpowerCanonical
  change decode factor = decode field.QM31.ONE + decode power at hfactorValue
  obtain ⟨product, hproduct, hproductCanonical, hproductValue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact factor g hfactorCanonical hg
  change decode product = decode factor * decode g at hproductValue
  obtain ⟨out, hout, houtCanonical, houtValue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact
      shared product hsharedCanonical hproductCanonical
  change decode out = decode shared + decode product at houtValue
  have hone : decode field.QM31.ONE = (1 : ExactQM) := by
    exact AspisR1.ExtractedMaskConstants.one_decode
  refine ⟨out, ?_, houtCanonical, ?_⟩
  · unfold state_only_hiding.state_only_selected_mask_value
    simp only [hlinears, bind_tc_ok]
    change (do
      let coefficients1 ← state_only_hiding.state_only_selected_mask_value_loop0
        range0 c1 initialCoefficients
      let coefficients2 ← state_only_hiding.state_only_selected_mask_value_loop1
        range1 maskOnly coefficients1
      let prepared ← field.PreparedQm31Multiplier.new linear
      let seed ← Array.index_usize coefficients2
        state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE
      let iter ← core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
        AspisR1.ExtractedMaskHornerCaller.sourceRange
      let shared ← state_only_hiding.state_only_selected_mask_value_loop2
        iter coefficients2 prepared seed
      let power ← state_only_hiding.mask_power_26 explicitLinear
      let factor ← field.QM31.add field.QM31.ONE power
      let product ← field.QM31.mul factor g
      field.QM31.add shared product) = .ok out
    simp only [hloop0, hloop1, hprepared, hseed, hreverse, hhorner,
      hpower, hfactor, hproduct, hout, bind_tc_ok]
  · change decode linear = _ at hlinearValue
    change decode explicitLinear = _ at hexplicitValue
    change decode power = decode explicitLinear ^ 26 at hpowerValue
    change decode shared =
      AspisR1.ExtractedMaskHornerPolynomial.coefficientPolynomial
        (AspisR1.ExtractedMaskHornerCaller.coefficientValue coefficients2)
        (decode linear) at hsharedValue
    rw [houtValue, hproductValue, hfactorValue, hone, hpowerValue,
      hexplicitValue, hsharedValue, hpopulated, hlinearValue]

#print axioms initialCoefficients_canonical
#print axioms selected_mask_value_populated_model

end AspisR1.ExtractedMaskCallerModel
