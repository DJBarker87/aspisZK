import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CompositionPartsCallerChunk07dV2
import TerminalV4TerminalPartsChunk08V2
import TerminalV4PublicTerminalQM31Chunk09V4
import TerminalV4PublicTerminalQM31ActualPartsChunk10V3
import TerminalV4PublicSemanticChunk11V2
import TerminalV4PublicTerminalQM31WithEvaluatorsChunk12V3
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe

theorem terminal_qm31_projects_source_parts_success
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (self : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array field.QM31 29#usize) 3#usize)
    (alpha : Array field.QM31 10#usize) (c : state_only_prefix.r0.Challenges)
    (selected : Array field.QM31 84#usize)
    (sem : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (out : field.QM31) (c1 : Array field.QM31 16#usize)
    (mask : Array field.QM31 10#usize) (g : field.QM31)
    (hgather : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO claims = .ok selected)
    (hsemantic : pool_v1.pair_forest_semantic_terminal.r0.Public.semantic self = .ok sem)
    (hparts : terminal_parts_from_composition_callers poseidonEval semanticEval
      sem selected alpha c.lambda c.chi c.theta c.zc c.mu =
      .ok (core.result.Result.Ok (out, c1, mask, g)))
    : terminal_qm31_with_evaluators poseidonEval semanticEval self claims alpha c =
      .ok (core.result.Result.Ok g) := by
  simp [terminal_qm31_with_evaluators,
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31_with_callers,
    hgather, hsemantic, hparts]

end AspisR1SelectedMaskProbe
