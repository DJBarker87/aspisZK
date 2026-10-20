import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4TerminalPartsChunk08V2
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe

/-- Exact source bridge for the post-composition terminal arithmetic.  The
caller premise is precisely the returned composition tuple; every subsequent
field operation is the generated terminal-parts body. -/
theorem terminal_parts_caller_to_arithmetic_tail
    (compositionCaller : TerminalPartsCompositionCaller)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (claims : Array field.QM31 84#usize)
    (point zerocheck_point : Array field.QM31 10#usize)
    (lambda chi theta mu composition h1_z copy_active : field.QM31)
    (c1 : Array field.QM31 16#usize)
    (mask_only : Array field.QM31 10#usize)
    (g : field.QM31)
    (hcaller : compositionCaller public1 claims point lambda chi theta =
      .ok (core.result.Result.Ok
        (composition, c1, mask_only, g, h1_z, copy_active))) :
    pool_v1.pair_forest_semantic_terminal.terminal_parts_with_caller
      compositionCaller public1 claims point lambda chi theta zerocheck_point mu =
    (do
      let q ← pool_v1.pair_forest_semantic_terminal.equality_value
        zerocheck_point point
      let q1 ← field.QM31.mul q composition
      let q2 ← field.QM31.mul mu h1_z
      let q3 ← field.QM31.add q1 q2
      let q4 ← field.QM31.mul mu mu
      let q5 ← field.QM31.sub field.QM31.ONE copy_active
      let q6 ← field.QM31.mul q5 h1_z
      let q7 ← field.QM31.mul q4 q6
      let original ← field.QM31.add q3 q7
      ok (core.result.Result.Ok (original, c1, mask_only, g))) := by
  unfold pool_v1.pair_forest_semantic_terminal.terminal_parts_with_caller
  rw [hcaller]
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rfl

end AspisR1SelectedMaskProbe
