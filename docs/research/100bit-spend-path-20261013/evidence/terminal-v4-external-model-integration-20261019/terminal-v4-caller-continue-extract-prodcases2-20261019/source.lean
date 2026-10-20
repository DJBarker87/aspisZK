import TerminalV4CompositionPartsCallerChunk07dV2
import TerminalV4CompositionContinueCanonicalV2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AspisR1.TerminalV4CompositionCallerContinueExtractV2
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31

theorem caller_success_extracts_continue_none
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (claims : Array QM 84#usize) (point : Array QM 10#usize)
    (lambda chi theta : QM)
    (composition : QM) (c1 : Array QM 16#usize) (mask : Array QM 10#usize)
    (g h1Z copyActive : QM)
    (hwithdrawal : public1.withdrawal_amount = none)
    (htransition : pool_v1.pair_forest_semantic_terminal.validate_transition
      { public1 with withdrawal_amount := none } = .ok (.Ok ()))
    (hcaller : pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
      poseidonEval semanticEval public1 claims point lambda chi theta =
      .ok (core.result.Result.Ok (composition, c1, mask, g, h1Z, copyActive))) :
    composition_parts_continue poseidonEval semanticEval public1 none claims point lambda chi theta =
      .ok (core.result.Result.Ok (composition, c1, mask, g, h1Z, copyActive)) := by
  unfold pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers at hcaller
  simp only [hwithdrawal, bind_tc_ok, Prod.casesOn] at hcaller
  simp only [htransition, bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hcaller
  exact hcaller

#print axioms caller_success_extracts_continue_none
end AspisR1.TerminalV4CompositionCallerContinueExtractV2
end
