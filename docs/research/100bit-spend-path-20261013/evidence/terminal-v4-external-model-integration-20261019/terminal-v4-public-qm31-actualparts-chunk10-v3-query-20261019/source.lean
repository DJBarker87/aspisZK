import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CompositionPartsCallerChunk07dV2
import TerminalV4TerminalPartsChunk08V2
import TerminalV4PublicTerminalQM31Chunk09V4
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe

def terminal_parts_from_composition_callers
  (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator) :
  TerminalQM31PartsCaller :=
  fun public1 claims point lambda chi theta zc mu =>
    pool_v1.pair_forest_semantic_terminal.terminal_parts_with_caller
      (fun public1 claims point lambda chi theta =>
        pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
          poseidonEval semanticEval public1 claims point lambda chi theta)
      public1 claims point lambda chi theta zc mu

end AspisR1SelectedMaskProbe
