import ExtractedMaskLinears
import ExtractedMaskLinearMomentBridge

/-! Draft only: compose the checked selected-mask wrapper contract with the
symbolic reverse-accumulator moment theorem. This remains a mathematical model
of the translated wrapper and makes no R0P/source-refinement claim. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskLinearsExact

open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskLinears.CanonicalQM

def decodedPoint (point : Array QM 10#usize) : Fin 10 → ExactQM :=
  fun i => AspisR1.ExtractedMaskLinears.decode
    (AspisR1.ExtractedMaskLinearLoop.pointAtNat point i.val i.isLt)

theorem pointValue_eq_pointOf (point : Array QM 10#usize) :
    AspisR1.ExtractedMaskLinearLoop.pointValue point =
      AspisR1.ExtractedMaskLinearMomentBridge.pointOf (decodedPoint point) := by
  funext i
  by_cases hi : i < 10
  · simp only [AspisR1.ExtractedMaskLinearLoop.pointValue, dif_pos hi]
    change AspisR1.ExtractedMaskLinearLoop.decode
      (AspisR1.ExtractedMaskLinearLoop.pointAtNat point i hi) =
      AspisR1.ExtractedMaskLinearMomentBridge.pointOf (decodedPoint point) i
    simp only [AspisR1.ExtractedMaskLinearMomentBridge.pointOf, dif_pos hi,
      decodedPoint, AspisR1.ExtractedMaskLinearLoop.pointAtNat,
      AspisR1.ExtractedMaskLinearLoop.decode,
      AspisR1.ExtractedMaskLinearStep.decode,
      AspisR1.ExtractedMaskLinears.decode]
  · simp [AspisR1.ExtractedMaskLinearLoop.pointValue,
      AspisR1.ExtractedMaskLinearMomentBridge.pointOf, hi]

/-- The two values returned by the actual extracted `selected_mask_linears`
wrapper decode to the two exact finite-field linear forms on its ten decoded
point cells. The canonicality assumptions are exactly those required by the
extracted scalar-multiplication and addition contracts. -/
theorem selected_mask_linears_exact_meaning
    (point : Array QM 10#usize)
    (hpoint : ∀ i : Nat, ∀ hi : i < 10,
      CanonicalQM (AspisR1.ExtractedMaskLinearLoop.pointAtNat point i hi)) :
    ∃ out : QM × QM,
      state_only_hiding.selected_mask_linears point = .ok out ∧
      CanonicalQM out.1 ∧ CanonicalQM out.2 ∧
      AspisR1.ExtractedMaskLinears.decode out.1 =
        AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0 (decodedPoint point) ∧
      AspisR1.ExtractedMaskLinears.decode out.2 =
        AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16 (decodedPoint point) := by
  obtain ⟨out, hrun, hcan0, hcan16, hvalue0, hvalue16⟩ :=
    AspisR1.ExtractedMaskLinears.selected_mask_linears_exact point hpoint
  obtain ⟨h3, h22, h275, h150⟩ :=
    AspisR1.ExtractedMaskLinears.scalarEmbedding_source_numerals
  have hvalue0' :
      AspisR1.ExtractedMaskLinears.decode out.1 =
        (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
          (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).1 * 3 +
        (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
          (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).2 * 22 := by
    simpa [h3, h22] using hvalue0
  have hvalue16' :
      AspisR1.ExtractedMaskLinears.decode out.2 =
        (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
          (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).1 * 275 +
        (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
          (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).2 * 150 := by
    simpa [h275, h150] using hvalue16
  have hmoments :=
    AspisR1.ExtractedMaskLinearMomentBridge.selected_outputs_of_accumulatorModel
      (decodedPoint point)
  have hmoments0 :
      (3 : ExactQM) *
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).1 +
        22 *
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).2 =
        AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0 (decodedPoint point) := by
    simpa [pointValue_eq_pointOf] using hmoments.1
  have hmoments16 :
      (275 : ExactQM) *
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).1 +
        150 *
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).2 =
        AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16 (decodedPoint point) := by
    simpa [pointValue_eq_pointOf] using hmoments.2
  refine ⟨out, hrun, hcan0, hcan16, ?_, ?_⟩
  · calc
      AspisR1.ExtractedMaskLinears.decode out.1 =
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).1 * 3 +
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).2 * 22 := hvalue0'
      _ = (3 : ExactQM) *
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).1 +
          22 *
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).2 := by ring
      _ = AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0 (decodedPoint point) := hmoments0
  · calc
      AspisR1.ExtractedMaskLinears.decode out.2 =
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).1 * 275 +
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).2 * 150 := hvalue16'
      _ = (275 : ExactQM) *
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).1 +
          150 *
          (AspisR1.ExtractedMaskLinearLoop.accumulatorModel
            (AspisR1.ExtractedMaskLinearLoop.pointValue point) 10 (0, 0)).2 := by ring
      _ = AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16 (decodedPoint point) := hmoments16

#print axioms pointValue_eq_pointOf
#print axioms selected_mask_linears_exact_meaning

end AspisR1.ExtractedMaskLinearsExact
