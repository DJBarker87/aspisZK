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
theorem terminal_success_inversion_diag
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (self : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array field.QM31 29#usize) 3#usize)
    (alpha : Array field.QM31 10#usize) (c : state_only_prefix.r0.Challenges)
    (out : field.QM31)
    (hsuccess : terminal_qm31_with_evaluators poseidonEval semanticEval self claims alpha c =
      .ok (core.result.Result.Ok out)) : True := by
  simp only [terminal_qm31_with_evaluators,
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31_with_callers] at hsuccess
  trace_state
  trivial
end AspisR1SelectedMaskProbe
