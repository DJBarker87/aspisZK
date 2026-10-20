import TerminalV4PublicTerminalQM31ActualPartsChunk10V2
import TerminalV4PublicTerminalQM31WithEvaluatorsChunk12V3
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1.TerminalV4PartsCallerInversion
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31

private theorem composition_success_of_parts_success
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (claims : Array QM 84#usize) (point : Array QM 10#usize)
    (lambda chi theta : QM)
    (out : QM) (c1 : Array QM 16#usize) (mask : Array QM 10#usize) (g : QM)
    (hparts : terminal_parts_from_composition_callers poseidonEval semanticEval
      public1 claims point lambda chi theta 0#usize 0#usize =
      .ok (core.result.Result.Ok (out, c1, mask, g))) :
    ∃ composition c1' mask' g' h1Z copyActive,
      pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
        poseidonEval semanticEval public1 claims point lambda chi theta =
        .ok (core.result.Result.Ok (composition, c1', mask', g', h1Z, copyActive)) := by
  unfold terminal_parts_from_composition_callers at hparts
  unfold pool_v1.pair_forest_semantic_terminal.terminal_parts_with_caller at hparts
  cases hcall : pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
      poseidonEval semanticEval public1 claims point lambda chi theta with
  | ok result =>
    cases result with
    | Ok tuple =>
      rcases tuple with ⟨composition, c1', mask', g', h1Z, copyActive⟩
      exact ⟨composition, c1', mask', g', h1Z, copyActive, hcall⟩
    | Err err => simp [hcall, bind_tc_ok] at hparts
  | fail err => simp [hcall, bind_tc_fail] at hparts
  | div => simp [hcall, bind_tc_div] at hparts

#print axioms composition_success_of_parts_success
end AspisR1.TerminalV4PartsCallerInversion
