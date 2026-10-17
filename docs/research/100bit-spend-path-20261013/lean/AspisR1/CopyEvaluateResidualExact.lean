import AspisR1.CopyEvaluateRowExact

/-! Source pattern/link row composed with the actual checked Copy residual. -/
set_option autoImplicit false
namespace AspisR1.CopyEvaluateResidualExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CopyEvaluateRowExact
open AspisR1.ArrayUpdateCanonicalExact (CanonicalArray)
open AspisR1.CopyEndpointExact (decodedCells modelSelectors)
open AspisR1.CopyLinkWeightExact (Variant modelVariant)

def residualPrefix (openings : Array QM 16#usize) (helper : QM)
    (selectors : Selectors) (lambda chi : QM) (index : U64) (variant : Variant) : Result QM := do
  let row ← rowPrefix openings selectors lambda index variant
  AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.copy_residual row helper chi

theorem residual_prefix_success (openings : Array QM 16#usize) (helper : QM)
    (selectors : Selectors) (lambda chi : QM) (index : U64) (variant : Variant)
    (hopenings : CanonicalArray openings)
    (hhigh : CanonicalArray selectors.high) (hlow : CanonicalArray selectors.low)
    (hlambda : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM lambda)
    (hhelper : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM helper)
    (hchi : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM chi) :
    ∃ out, residualPrefix openings helper selectors lambda chi index variant = .ok out ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM out ∧
      decode out = R0P.copyResidual
        (retainedRow (decodedCells openings) (modelSelectors selectors)
          (decode lambda) index.val (modelVariant variant)) (decode helper) (decode chi) := by
  obtain ⟨row,hrow,hpv,hpw,hcv,hcw,hmodel⟩ :=
    row_prefix_success openings selectors lambda index variant hopenings hhigh hlow hlambda
  obtain ⟨out,hrun,hcanonical,hvalue⟩ :=
    AspisR1.CopyResidualExact.copy_residual_exact row helper chi hpv hpw hcv hcw hhelper hchi
  refine ⟨out,?_,hcanonical,?_⟩
  · simp only [residualPrefix,hrow,hrun,bind_tc_ok]
  · exact hvalue.trans (congrArg (fun r : R0P.CopyRowExtension ExactQM =>
      R0P.copyResidual r (decode helper) (decode chi)) hmodel)

#print axioms residual_prefix_success
end
end AspisR1.CopyEvaluateResidualExact
