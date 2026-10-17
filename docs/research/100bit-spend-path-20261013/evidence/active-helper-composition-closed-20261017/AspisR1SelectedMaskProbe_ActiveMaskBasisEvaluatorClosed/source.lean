import AspisR1SelectedMaskProbe.ActiveMaskBasisComplete
import AspisR1.CopyEvaluatorExact

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisEvaluatorClosed

abbrev QM := field.QM31
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Variant := AspisR1.CopyLinkWeightExact.Variant
abbrev Output := AspisR1.CopyEvaluatorFactor.Output
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.ArrayUpdateCanonicalExact.CanonicalArray a

attribute [local irreducible] R0P.copyLinks R0P.copyEvaluateWithSelectors
  AspisR1.CopyEvaluateRowExact.retainedRow R0P.copyResidual R0P.copyActiveLiteral R0P.activeMaskBasisModel

theorem evaluate_success
    (openings : Array QM 16#usize) (helper : QM) (selectors : Selectors)
    (lambda chi : QM) (index : U64) (variant : Variant)
    (hopenings : CanonicalArray openings)
    (hhigh : CanonicalArray selectors.high) (hlow : CanonicalArray selectors.low)
    (hlambda : CanonicalQM lambda) (hhelper : CanonicalQM helper) (hchi : CanonicalQM chi) :
    ∃ out : Output,
      AspisR1.CopyEvaluatorFactor.evaluate openings helper selectors lambda chi index variant = .ok out ∧
      CanonicalQM out.residual ∧ CanonicalQM out.active ∧
      (AspisR1.ExtractedMaskQM31Exact.decode out.residual,
        AspisR1.ExtractedMaskQM31Exact.decode out.active) =
        R0P.copyEvaluateWithSelectors
          (AspisR1.CopyEndpointExact.decodedCells openings)
          (AspisR1.ExtractedMaskQM31Exact.decode helper)
          (AspisR1.CopyEndpointExact.modelSelectors selectors)
          (AspisR1.ExtractedMaskQM31Exact.decode lambda)
          (AspisR1.ExtractedMaskQM31Exact.decode chi) index.val
          (AspisR1.CopyLinkWeightExact.modelVariant variant) := by
  apply AspisR1.CopyEvaluatorExact.evaluate_success_of_active
    openings helper selectors lambda chi index variant hopenings hhigh hlow
    hlambda hhelper hchi
  obtain ⟨active, hrun, hcanonical, hdecode⟩ :=
    AspisR1SelectedMaskProbe.ActiveMaskBasisComplete.active_mask_basis_success
      selectors hhigh hlow
  exact ⟨active, hrun, hcanonical, hdecode.trans
    (R0P.copy_active_literal_eq_active_mask_basis
      (AspisR1.CopyEndpointExact.modelSelectors selectors)).symm⟩

#print axioms evaluate_success
end AspisR1SelectedMaskProbe.ActiveMaskBasisEvaluatorClosed
