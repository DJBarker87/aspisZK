import AspisR1.CopyPatternValuesExact
import AspisR1.CopyLinkLoopFuel
import AspisR1.ArrayZeroExact
import CopyResidualExact

/-! The exact pre-active fragment of evaluate_with_selectors, composing source
pattern generation with the full link traversal and retained row model. -/
set_option autoImplicit false
namespace AspisR1.CopyEvaluateRowExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ArrayUpdateCanonicalExact (CanonicalArray)
open AspisR1.CopyEndpointExact (decodedCells modelSelectors)
open AspisR1.CopyLinkWeightExact (Variant modelVariant)
abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Row := AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.CopyRowExtension
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

def rowPrefix (openings : Array QM 16#usize) (selectors : Selectors)
    (lambda : QM) (index : U64) (variant : Variant) : Result Row := do
  let patterns ← AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values openings lambda
  let a := Array.repeat 2#usize field.QM31.ZERO
  let a1 := Array.repeat 2#usize field.QM31.ZERO
  let a2 := Array.repeat 2#usize field.QM31.ZERO
  let a3 := Array.repeat 2#usize field.QM31.ZERO
  let (pv,pw,cv,cw) ←
    AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop
      selectors index variant patterns a a1 a2 a3 0#usize
  ok { producer_values := pv, producer_weights := pw,
       consumer_values := cv, consumer_weights := cw }

def retainedRow (openings : Fin 16 → ExactQM) (selectors : R0P.CopySelectors ExactQM)
    (lambda : ExactQM) (index : Nat) (variant : R0P.Variant) : R0P.CopyRowExtension ExactQM :=
  R0P.copyLinks.foldl
    (fun acc link => AspisR1.CopyLinkStepExact.modelStep acc link index variant
      (R0P.copyPatternValuesLiteral openings lambda) selectors)
    ⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩

theorem row_prefix_success (openings : Array QM 16#usize) (selectors : Selectors)
    (lambda : QM) (index : U64) (variant : Variant)
    (hopenings : CanonicalArray openings)
    (hhigh : CanonicalArray selectors.high) (hlow : CanonicalArray selectors.low)
    (hlambda : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM lambda) :
    ∃ row, rowPrefix openings selectors lambda index variant = .ok row ∧
      CanonicalArray row.producer_values ∧ CanonicalArray row.producer_weights ∧
      CanonicalArray row.consumer_values ∧ CanonicalArray row.consumer_weights ∧
      AspisR1.CopyResidualExact.modelRow row =
        retainedRow (decodedCells openings) (modelSelectors selectors)
          (decode lambda) index.val (modelVariant variant) := by
  obtain ⟨patterns,hpatternsRun,hpatterns,hpatternsModel⟩ :=
    AspisR1.CopyPatternValuesExact.patterns_success openings lambda hopenings hlambda
  let zeros := Array.repeat 2#usize field.QM31.ZERO
  have hczeros : CanonicalArray zeros := AspisR1.ArrayZeroExact.repeat_zero_canonical
  obtain ⟨pv,pw,cv,cw,hloop,hpv,hpw,hcv,hcw,hmodel⟩ :=
    AspisR1.CopyLinkLoopFuel.loop_success selectors index variant patterns zeros zeros zeros zeros
      hpatterns hhigh hlow hczeros hczeros hczeros hczeros
  have hzeroRow : AspisR1.CopyLinkStepExact.modelRow zeros zeros zeros zeros =
      (⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩ : R0P.CopyRowExtension ExactQM) := by
    unfold AspisR1.CopyLinkStepExact.modelRow
    dsimp only [zeros]
    rw [AspisR1.ArrayZeroExact.repeat_zero_decoded]
    rfl
  change decodedCells patterns =
    R0P.copyPatternValuesLiteral (decodedCells openings) (decode lambda) at hpatternsModel
  let row : Row := ⟨pv,pw,cv,cw⟩
  refine ⟨row,?_,hpv,hpw,hcv,hcw,?_⟩
  · dsimp only [zeros,AspisR1.CopyLinkLoopFactor.loopFn] at hloop
    simp only [rowPrefix,hpatternsRun,hloop,bind_tc_ok]
    rfl
  · change AspisR1.CopyLinkStepExact.modelRow pv pw cv cw = _
    have hp := congrArg (fun pats : Fin 14 → ExactQM =>
      R0P.copyLinks.foldl (fun acc link => AspisR1.CopyLinkStepExact.modelStep
        acc link index.val (modelVariant variant) pats (modelSelectors selectors))
        (AspisR1.CopyLinkStepExact.modelRow zeros zeros zeros zeros)) hpatternsModel
    have hz := congrArg (fun initial : R0P.CopyRowExtension ExactQM =>
      R0P.copyLinks.foldl (fun acc link => AspisR1.CopyLinkStepExact.modelStep
        acc link index.val (modelVariant variant)
        (R0P.copyPatternValuesLiteral (decodedCells openings) (decode lambda))
        (modelSelectors selectors)) initial) hzeroRow
    exact hmodel.trans (hp.trans hz)

#print axioms row_prefix_success
end
end AspisR1.CopyEvaluateRowExact
