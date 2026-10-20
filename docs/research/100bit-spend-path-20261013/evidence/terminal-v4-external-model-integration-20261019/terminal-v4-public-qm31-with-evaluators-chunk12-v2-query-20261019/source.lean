import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CompositionPartsCallerChunk07dV2
import TerminalV4TerminalPartsChunk08V2
import TerminalV4PublicTerminalQM31Chunk09V4
import TerminalV4PublicTerminalQM31ActualPartsChunk10V2
import TerminalV4PublicSemanticChunk11V2
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe

def terminal_qm31_with_evaluators
  (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (claims : Array (Array field.QM31 29#usize) 3#usize)
  (alpha : Array field.QM31 10#usize) (c : state_only_prefix.r0.Challenges) :
  Result (core.result.Result field.QM31 state_only_prefix.r0.Error) :=
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31_with_callers
    pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
    (terminal_parts_from_composition_callers poseidonEval semanticEval)
    self claims alpha c

end AspisR1SelectedMaskProbe
