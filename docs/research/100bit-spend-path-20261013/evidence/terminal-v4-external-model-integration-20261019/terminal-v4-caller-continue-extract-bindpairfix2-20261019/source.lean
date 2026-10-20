import TerminalV4CompositionPartsCallerChunk07dV2
import AspisR1.TerminalV4ResultBindPairSuccessV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AspisR1.TerminalV4CompositionCallerContinueExtractV6
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev ErrorT := pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
abbrev ContinueResult := Result (core.result.Result
  (QM × Array QM 16#usize × Array QM 10#usize × QM × QM × QM) ErrorT)

def amountPrefix (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic) :
    Result (Option Std.U32 × Bool) :=
  match public1.withdrawal_amount with
  | none => ok (none, false)
  | some amount => do
    let b : Bool ←
      if amount = 0#u32 then ok true else do
        let i ← 1#u32 <<< 30#u32
        ok (amount >= i)
    ok (public1.withdrawal_amount, b)

def afterAmountPrefix
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (claims : Array QM 84#usize) (point : Array QM 10#usize)
    (lambda chi theta : QM) (o : Option Std.U32) (invalid : Bool) : ContinueResult := do
  if invalid then
    ok (core.result.Result.Err
      pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidPublicAmount)
  else do
    let r ← pool_v1.pair_forest_semantic_terminal.validate_transition
      { public1 with withdrawal_amount := o }
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      composition_parts_continue poseidonEval semanticEval public1 o claims point lambda chi theta
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (QM × Array QM 16#usize × Array QM 10#usize × QM × QM × QM)
        (core.convert.FromSame ErrorT) residual

theorem caller_eq_bindPair (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (claims : Array QM 84#usize) (point : Array QM 10#usize)
    (lambda chi theta : QM) :
    pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
      poseidonEval semanticEval public1 claims point lambda chi theta =
    AspisR1.TerminalV4ResultBindPairSuccessV1.bindPair (amountPrefix public1)
      (afterAmountPrefix poseidonEval semanticEval public1 claims point lambda chi theta) := by
  rfl

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
  rw [caller_eq_bindPair] at hcaller
  obtain ⟨o, invalid, hpref, hrest⟩ :=
    AspisR1.TerminalV4ResultBindPairSuccessV1.bindPair_ok_inv
      (amountPrefix public1)
      (afterAmountPrefix poseidonEval semanticEval public1 claims point lambda chi theta)
      (core.result.Result.Ok (composition, c1, mask, g, h1Z, copyActive)) hcaller
  by_cases hb : invalid = true
  · simp [afterAmountPrefix, hb] at hrest
  · have hv := htransition o
    simp [afterAmountPrefix, hb, hv,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hrest
    exact ⟨o, hrest⟩

#print axioms caller_eq_bindPair
#print axioms caller_success_extracts_continue
end AspisR1.TerminalV4CompositionCallerContinueExtractV6
end
