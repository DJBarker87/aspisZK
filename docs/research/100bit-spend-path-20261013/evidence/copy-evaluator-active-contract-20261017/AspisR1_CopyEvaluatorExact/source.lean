import AspisR1.CopyEvaluatorFactor
import AspisR1.CopyEvaluatorModel

/-! Candidate full evaluator, with only the active helper execution/model
contract left explicit. All other source operations are derived below. -/
set_option autoImplicit false
namespace AspisR1.CopyEvaluatorExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CopyEvaluateRowExact (QM ExactQM Selectors decode row_prefix_success retainedRow)
open AspisR1.CopyLinkWeightExact (Variant modelVariant)
open AspisR1.CopyEndpointExact (decodedCells modelSelectors)
open AspisR1.ArrayUpdateCanonicalExact (CanonicalArray)
open AspisR1.CopyEvaluatorFactor (evaluate Output)
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
attribute [local irreducible] R0P.copyLinks R0P.copyEvaluateWithSelectors
  AspisR1.CopyEvaluateRowExact.retainedRow R0P.copyResidual R0P.copyActiveLiteral

theorem evaluate_success_of_active (openings : Array QM 16#usize) (helper : QM)
    (selectors : Selectors) (lambda chi : QM) (index : U64) (variant : Variant)
    (hopenings : CanonicalArray openings)
    (hhigh : CanonicalArray selectors.high) (hlow : CanonicalArray selectors.low)
    (hlambda : CanonicalQM lambda) (hhelper : CanonicalQM helper) (hchi : CanonicalQM chi)
    (hactive : ∃ a,
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis selectors = .ok a ∧
      CanonicalQM a ∧ decode a = R0P.copyActiveLiteral (modelSelectors selectors)) :
    ∃ out : Output, evaluate openings helper selectors lambda chi index variant = .ok out ∧
      CanonicalQM out.residual ∧ CanonicalQM out.active ∧
      (decode out.residual,decode out.active) =
        R0P.copyEvaluateWithSelectors (decodedCells openings) (decode helper)
          (modelSelectors selectors) (decode lambda) (decode chi) index.val (modelVariant variant) := by
  obtain ⟨row,hrow,hpv,hpw,hcv,hcw,hrowModel⟩ :=
    row_prefix_success openings selectors lambda index variant hopenings hhigh hlow hlambda
  obtain ⟨active,hactiveRun,hcactive,hvactive⟩ := hactive
  have hsourceActive : AspisR1.CopyEvaluatorFactor.active selectors = .ok active := hactiveRun
  obtain ⟨residual,hresidual,hcresidual,hvresidual⟩ :=
    AspisR1.CopyResidualExact.copy_residual_exact row helper chi hpv hpw hcv hcw hhelper hchi
  have hvresidualModel : decode residual =
      R0P.copyResidual (retainedRow (decodedCells openings) (modelSelectors selectors)
        (decode lambda) index.val (modelVariant variant)) (decode helper) (decode chi) :=
    hvresidual.trans (congrArg (fun r : R0P.CopyRowExtension ExactQM =>
      R0P.copyResidual r (decode helper) (decode chi)) hrowModel)
  obtain ⟨value,hmul,hcvalue,hvvalue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact active residual hcactive hcresidual
  change decode value = decode active * decode residual at hvvalue
  let out : Output := ⟨value,active⟩
  refine ⟨out,?_,hcvalue,hcactive,?_⟩
  · rw [AspisR1.CopyEvaluatorFactor.evaluate_eq_row_prefix]
    simp only [hrow,hsourceActive,hresidual,hmul,bind_tc_ok]
    rfl
  · change (decode value,decode active) = _
    have hdecoded : (decode value,decode active) =
        (R0P.copyActiveLiteral (modelSelectors selectors) *
          R0P.copyResidual (retainedRow (decodedCells openings) (modelSelectors selectors)
            (decode lambda) index.val (modelVariant variant)) (decode helper) (decode chi),
         R0P.copyActiveLiteral (modelSelectors selectors)) :=
      Prod.ext
        (hvvalue.trans (congrArg₂ (fun x y : ExactQM => x * y) hvactive hvresidualModel)) hvactive
    exact hdecoded.trans (AspisR1.CopyEvaluatorModel.retained_evaluator_eq
      (decodedCells openings) (decode helper) (modelSelectors selectors)
      (decode lambda) (decode chi) index.val (modelVariant variant)).symm

#print axioms evaluate_success_of_active
end
end AspisR1.CopyEvaluatorExact
