import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4PublicTerminalQM31WithEvaluatorsChunk12V3
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

theorem terminal_success_reaches_parts
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (self : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array field.QM31 29#usize) 3#usize)
    (alpha : Array field.QM31 10#usize) (c : state_only_prefix.r0.Challenges)
    (out : field.QM31)
    (hsuccess : terminal_qm31_with_evaluators poseidonEval semanticEval self claims alpha c =
      .ok (core.result.Result.Ok out)) :
    ∃ selected sem tuple,
      array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
        pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims = .ok selected ∧
      pool_v1.pair_forest_semantic_terminal.r0.Public.semantic self = .ok sem ∧
      terminal_parts_from_composition_callers poseidonEval semanticEval
        sem selected alpha c.lambda c.chi c.theta c.zc c.mu =
        .ok (core.result.Result.Ok tuple) ∧
      tuple.1 = out := by
  unfold terminal_qm31_with_evaluators
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31_with_callers at hsuccess
  cases hgather : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO claims with
  | ok selected =>
    simp only [hgather, bind_tc_ok] at hsuccess
    cases hsemantic : pool_v1.pair_forest_semantic_terminal.r0.Public.semantic self with
    | ok sem =>
      simp only [hsemantic, bind_tc_ok] at hsuccess
      cases hparts : terminal_parts_from_composition_callers poseidonEval semanticEval
          sem selected alpha c.lambda c.chi c.theta c.zc c.mu with
      | ok result =>
        simp only [hparts, bind_tc_ok,
          AspisR1SelectedMaskProbe.core.result.Result.map,
          pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31.call_once,
          AspisR1SelectedMaskProbe.core.result.Result.map_err] at hsuccess
        cases result with
        | Ok tuple =>
          have hfirst : tuple.1 = out := by
            injection hsuccess with hproj
            exact hproj
          exact ⟨selected, sem, tuple, rfl, rfl, rfl, hfirst⟩
        | Err e => simp at hsuccess
      | fail e => simp [hparts] at hsuccess
      | div => simp [hparts] at hsuccess
    | fail e => simp [hsemantic] at hsuccess
    | div => simp [hsemantic] at hsuccess
  | fail e => simp [hgather] at hsuccess
  | div => simp [hgather] at hsuccess

#print axioms terminal_success_reaches_parts
end AspisR1SelectedMaskProbe
