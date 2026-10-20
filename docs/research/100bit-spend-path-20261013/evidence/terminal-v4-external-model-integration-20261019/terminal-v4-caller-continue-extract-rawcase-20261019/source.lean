import TerminalV4CompositionPartsCallerChunk07dV2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AspisR1.TerminalV4CompositionCallerContinueExtractV5
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31

theorem caller_success_extracts_continue
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (claims : Array QM 84#usize) (point : Array QM 10#usize)
    (lambda chi theta : QM)
    (composition : QM) (c1 : Array QM 16#usize) (mask : Array QM 10#usize)
    (g h1Z copyActive : QM)
    (htransition : ∀ o : Option Std.U32,
      pool_v1.pair_forest_semantic_terminal.validate_transition
        { public1 with withdrawal_amount := o } = .ok (.Ok ()))
    (hcaller : pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
      poseidonEval semanticEval public1 claims point lambda chi theta =
      .ok (core.result.Result.Ok (composition, c1, mask, g, h1Z, copyActive))) :
    ∃ o, composition_parts_continue poseidonEval semanticEval public1 o claims point lambda chi theta =
      .ok (core.result.Result.Ok (composition, c1, mask, g, h1Z, copyActive)) := by
  unfold pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers at hcaller
  cases hp : (match public1.withdrawal_amount with
    | none => ok (none, false)
    | some amount => do
      let b : Bool ←
        if amount = 0#u32 then ok true else do
          let i ← 1#u32 <<< 30#u32
          ok (decide (↑i ≤ ↑amount))
      ok (public1.withdrawal_amount, b)) with
  | ok pair =>
    cases pair with
    | mk o invalid =>
      have hv := htransition o
      simp only [hp, bind_tc_ok] at hcaller
      by_cases hb : invalid = true
      · simp [hb] at hcaller
      · simp [hb, hv, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hcaller
        exact ⟨o, hcaller⟩
  | fail err => simp [hp, bind_tc_fail] at hcaller
  | div => simp [hp, bind_tc_div] at hcaller

#print axioms caller_success_extracts_continue
end AspisR1.TerminalV4CompositionCallerContinueExtractV5
end
