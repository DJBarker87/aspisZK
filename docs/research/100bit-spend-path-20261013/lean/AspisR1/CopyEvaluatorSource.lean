import AspisR1.CopyEvaluateRowExact
import AspisR1SelectedMaskProbe.ActiveMaskBasisSourceSlice

/-! Candidate Copy evaluator with the selected active-basis feature route.
All source evaluator operations/order are retained; helper owners are shared. -/
set_option autoImplicit false
namespace AspisR1.CopyEvaluatorSource
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

structure pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1
  where
  residual : field.QM31
  active : field.QM31

/-- The active route selected by the candidate's existing basis feature. -/
def pool_v1.pair_forest_copy_terminal.Selectors.active
    (self : AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors) :
    Result field.QM31 := do
  AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis self

def pool_v1.pair_forest_copy_terminal.evaluate_with_selectors
  (openings : Array field.QM31 16#usize) (h1_z : field.QM31)
  (selectors : AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors)
  (lambda : field.QM31) (chi : field.QM31) (append_index : Std.U64)
  (variant :
  AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1) :
  Result
    pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1
  := do
  let patterns ←
    AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values openings lambda
  let a := Array.repeat 2#usize field.QM31.ZERO
  let a1 := Array.repeat 2#usize field.QM31.ZERO
  let a2 := Array.repeat 2#usize field.QM31.ZERO
  let a3 := Array.repeat 2#usize field.QM31.ZERO
  let (a4, a5, a6, a7) ←
    AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop selectors
      append_index variant patterns a a1 a2 a3 0#usize
  let active ← pool_v1.pair_forest_copy_terminal.Selectors.active selectors
  let q ←
    AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.copy_residual
      {
        producer_values := a4,
        producer_weights := a5,
        consumer_values := a6,
        consumer_weights := a7
      } h1_z chi
  let q1 ← field.QM31.mul active q
  ok { residual := q1, active }

end AspisR1.CopyEvaluatorSource
