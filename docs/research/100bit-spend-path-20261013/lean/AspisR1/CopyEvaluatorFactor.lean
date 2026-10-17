import AspisR1.CopyEvaluatorSource
import AspisR1.ResultPackSequence

/-! Exact evaluator factorization through the already proved pre-active row. -/
set_option autoImplicit false
namespace AspisR1.CopyEvaluatorFactor
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CopyEvaluateRowExact (QM Selectors)
open AspisR1.CopyLinkWeightExact (Variant)
abbrev Output := AspisR1.CopyEvaluatorSource.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1
abbrev evaluate := AspisR1.CopyEvaluatorSource.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors
abbrev active := AspisR1.CopyEvaluatorSource.pool_v1.pair_forest_copy_terminal.Selectors.active

theorem evaluate_eq_row_prefix (openings : Array QM 16#usize) (helper : QM)
    (selectors : Selectors) (lambda chi : QM) (index : U64) (variant : Variant) :
    evaluate openings helper selectors lambda chi index variant = (do
      let row ← AspisR1.CopyEvaluateRowExact.rowPrefix openings selectors lambda index variant
      let a ← active selectors
      let residual ← AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.copy_residual row helper chi
      let value ← field.QM31.mul a residual
      ok ({ residual := value, active := a } : Output)) := by
  unfold evaluate AspisR1.CopyEvaluatorSource.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors
    AspisR1.CopyEvaluateRowExact.rowPrefix
  exact AspisR1.ResultPackSequence.first_bind_packed_four
    (AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values openings lambda)
    (fun patterns => AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop
      selectors index variant patterns (Array.repeat 2#usize field.QM31.ZERO)
      (Array.repeat 2#usize field.QM31.ZERO) (Array.repeat 2#usize field.QM31.ZERO)
      (Array.repeat 2#usize field.QM31.ZERO) 0#usize)
    (fun pv pw cv cw =>
      ({ producer_values := pv
         producer_weights := pw
         consumer_values := cv
         consumer_weights := cw } : AspisR1.CopyEvaluateRowExact.Row))
    (fun row => do
      let a ← active selectors
      let residual ← AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.copy_residual row helper chi
      let value ← field.QM31.mul a residual
      ok ({ residual := value, active := a } : Output))

#print axioms evaluate_eq_row_prefix
end AspisR1.CopyEvaluatorFactor
