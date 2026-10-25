import ExtractedMaskLinearLoop
import ExtractedMaskScalarExact
import ExtractedMaskQM31Exact

/-! Draft operation contract for the actual extracted
`selected_mask_linears` wrapper. It instantiates the checked loop at the
literal reverse range and composes four scalar multiplications and two adds.
The loop result remains stated through `accumulatorModel`; the later moment
bridge is intentionally not imported. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskLinears

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev ReverseRange := AspisR1.ExtractedMaskReverseRange.ReverseRange

def decode (x : QM) : ExactQM := AspisR1.ExtractedMaskQM31Exact.decode x

def scalarEmbedding (x : field.M31) : ExactQM :=
  AspisR1.ExtractedMaskScalarExact.scalarEmbedding x

private theorem zero_canonical : CanonicalQM field.QM31.ZERO := by
  simp [CanonicalQM, AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
    AspisR1.ExtractedMaskTowerAdd.CanonicalCM, field.QM31.ZERO,
    AspisR1.ExtractedMaskTowerAdd.P, AspisR1.ExtractedMaskM31AddSub.P]

private theorem zero_decode : decode field.QM31.ZERO = 0 := by
  change AspisR1.ExtractedMaskQM31Exact.decode field.QM31.ZERO = 0
  ext <;> simp [AspisR1.ExtractedMaskQM31Exact.decode, field.QM31.ZERO]

private def sourceRange : core.ops.range.Range Usize :=
  { start := 0#usize, «end» := 10#usize }

private def sourceReverseRange : ReverseRange := ⟨sourceRange⟩

private theorem source_reverse_range_ok :
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      sourceRange = .ok sourceReverseRange := rfl

theorem selected_mask_linears_exact
    (point : Array QM 10#usize)
    (hpoint : ∀ i : Nat, ∀ hi : i < 10,
      CanonicalQM (AspisR1.ExtractedMaskLinearLoop.pointAtNat point i hi)) :
    ∃ out : QM × QM,
      state_only_hiding.selected_mask_linears point = .ok out ∧
      CanonicalQM out.1 ∧ CanonicalQM out.2 ∧
      decode out.1 =
        (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
          (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10
          (0, 0)).1 * scalarEmbedding (3#u32) +
        (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
          (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10
          (0, 0)).2 * scalarEmbedding (22#u32) ∧
      decode out.2 =
        (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
          (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10
          (0, 0)).1 * scalarEmbedding (275#u32) +
        (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
          (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10
          (0, 0)).2 * scalarEmbedding (150#u32) := by
  let model := AspisR1.ExtractedMaskLinearLoop.accumulatorModel
    (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)
  have hloop := AspisR1.ExtractedMaskLinearLoop.body_loop0_model
    point sourceReverseRange 10 field.QM31.ZERO field.QM31.ZERO rfl rfl
    (by omega) hpoint zero_canonical zero_canonical
  obtain ⟨⟨suffix, weighted⟩, hloopRun, hsuffix, hweighted, hmodel⟩ := hloop
  have hmodelPair : (decode suffix, decode weighted) = model := by
    change (decode suffix, decode weighted) =
      AspisR1.ExtractedMaskLinearLoop.accumulatorModel
        (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10
        (decode field.QM31.ZERO, decode field.QM31.ZERO) at hmodel
    rw [zero_decode] at hmodel
    simpa [model] using hmodel
  have hmodelSuffix : decode suffix = model.1 := by
    exact congrArg Prod.fst hmodelPair
  have hmodelWeighted : decode weighted = model.2 := by
    exact congrArg Prod.snd hmodelPair
  obtain ⟨q3, hq3, hcan3, hd3⟩ :=
    AspisR1.ExtractedMaskScalarExact.current_qm_mul_m31_exact suffix (3#u32)
  obtain ⟨q22, hq22, hcan22, hd22⟩ :=
    AspisR1.ExtractedMaskScalarExact.current_qm_mul_m31_exact weighted (22#u32)
  obtain ⟨linear, hlinear, hcanLinear, hdLinear⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q3 q22 hcan3 hcan22
  obtain ⟨q275, hq275, hcan275, hd275⟩ :=
    AspisR1.ExtractedMaskScalarExact.current_qm_mul_m31_exact suffix (275#u32)
  obtain ⟨q150, hq150, hcan150, hd150⟩ :=
    AspisR1.ExtractedMaskScalarExact.current_qm_mul_m31_exact weighted (150#u32)
  obtain ⟨explicitLinear, hexplicit, hcanExplicit, hdExplicit⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact
      q275 q150 hcan275 hcan150
  have hlineValue : decode linear = model.1 * scalarEmbedding (3#u32) +
      model.2 * scalarEmbedding (22#u32) := by
    change AspisR1.ExtractedMaskQM31Exact.decode linear =
      model.1 * AspisR1.ExtractedMaskScalarExact.scalarEmbedding (3#u32) +
        model.2 * AspisR1.ExtractedMaskScalarExact.scalarEmbedding (22#u32)
    change AspisR1.ExtractedMaskQM31Exact.decode suffix = model.1 at hmodelSuffix
    change AspisR1.ExtractedMaskQM31Exact.decode weighted = model.2 at hmodelWeighted
    rw [hdLinear, hd3, hd22, hmodelSuffix, hmodelWeighted]
  have hexplicitValue : decode explicitLinear =
      model.1 * scalarEmbedding (275#u32) +
      model.2 * scalarEmbedding (150#u32) := by
    change AspisR1.ExtractedMaskQM31Exact.decode explicitLinear =
      model.1 * AspisR1.ExtractedMaskScalarExact.scalarEmbedding (275#u32) +
        model.2 * AspisR1.ExtractedMaskScalarExact.scalarEmbedding (150#u32)
    change AspisR1.ExtractedMaskQM31Exact.decode suffix = model.1 at hmodelSuffix
    change AspisR1.ExtractedMaskQM31Exact.decode weighted = model.2 at hmodelWeighted
    rw [hdExplicit, hd275, hd150, hmodelSuffix, hmodelWeighted]
  refine ⟨(linear, explicitLinear), ?_, hcanLinear, hcanExplicit,
    hlineValue, hexplicitValue⟩
  have hrev :
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
        { start := 0#usize,
          «end» := state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS } =
        .ok sourceReverseRange := by
    simpa [sourceRange, sourceReverseRange,
      state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS] using
        source_reverse_range_ok
  unfold state_only_hiding.selected_mask_linears
  simp only [hrev, hloopRun, hq3, hq22, hlinear, hq275, hq150,
    hexplicit, bind_tc_ok]

/-- The four source coefficients are their corresponding exact tower
numerals under the explicit base-field scalar embedding. -/
theorem scalarEmbedding_source_numerals :
    scalarEmbedding (3#u32) = (3 : ExactQM) ∧
    scalarEmbedding (22#u32) = (22 : ExactQM) ∧
    scalarEmbedding (275#u32) = (275 : ExactQM) ∧
    scalarEmbedding (150#u32) = (150 : ExactQM) := by
  constructor
  · ext <;> norm_num [scalarEmbedding, AspisR1.ExtractedMaskScalarExact.scalarEmbedding,
      AspisV8R15.ExactTowerBase.QM31Exact,
      AspisV8R15.ExactTowerBase.CM31Exact,
      AspisV8R15.ExactTowerBase.M31Exact,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  constructor
  · ext <;> norm_num [scalarEmbedding, AspisR1.ExtractedMaskScalarExact.scalarEmbedding,
      AspisV8R15.ExactTowerBase.QM31Exact,
      AspisV8R15.ExactTowerBase.CM31Exact,
      AspisV8R15.ExactTowerBase.M31Exact,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  constructor
  · ext <;> norm_num [scalarEmbedding, AspisR1.ExtractedMaskScalarExact.scalarEmbedding,
      AspisV8R15.ExactTowerBase.QM31Exact,
      AspisV8R15.ExactTowerBase.CM31Exact,
      AspisV8R15.ExactTowerBase.M31Exact,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  · ext <;> norm_num [scalarEmbedding, AspisR1.ExtractedMaskScalarExact.scalarEmbedding,
      AspisV8R15.ExactTowerBase.QM31Exact,
      AspisV8R15.ExactTowerBase.CM31Exact,
      AspisV8R15.ExactTowerBase.M31Exact,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

#print axioms zero_canonical
#print axioms zero_decode
#print axioms selected_mask_linears_exact
#print axioms scalarEmbedding_source_numerals

end AspisR1.ExtractedMaskLinears
