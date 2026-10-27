import JFs_PublicComparisons
import JFs_PublicEncoders
import JFs_PublicLane
set_option autoImplicit false
namespace AspisR1.JFs_PublicValidation
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

theorem source : validate_pool_v1_pair_forest_terminal_statement_v1 JFs_PublicValue.value=ok (.Ok ()) := by
  obtain ⟨encoded,contents,payment⟩:=JFs_PublicEncoders.payment
  obtain ⟨updated,late,length⟩:=JFs_PublicEncoders.late
  have common : PoolV1PairForestTerminalStatementV1.common JFs_PublicValue.value=ok JFs_PublicValue.common := by rfl
  have publicCall : statement_public_common JFs_PublicValue.value=
      ok (JFs_PaymentValue.common.pool,JFs_PaymentValue.common.deployment_domain,
        JFs_PaymentValue.common.anchor_sequence,JFs_PaymentValue.common.anchor_root,
        JFs_PaymentValue.common.nullifier,JFs_PaymentValue.common.asset_id) := by rfl
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
  rw [common]
  simp only [bind_tc_ok,JFs_PublicValue.master_nonzero,JFs_PublicValue.checkpoint_nonzero,
    JFs_PublicValue.lane_nonzero,Bool.false_eq_true,↓reduceIte,lift,JFs_PublicComparisons.lane_bound]
  rw [show JFs_PublicValue.value=.PrivateTransfer JFs_PublicValue.common JFs_PaymentValue.value from rfl]
  simp only [payment,bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  dsimp only [JFs_PublicValue.value] at publicCall
  rw [publicCall]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        s.startsWith "AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1" &&
          (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  try simp (config := { zeta := true, iota := true }) only
  simp only [bind_tc_ok,JFs_PublicComparisons.pool,JFs_PublicComparisons.domain,
    JFs_PublicComparisons.snapshot_pool,JFs_PublicComparisons.anchor,JFs_PublicComparisons.sequence,
    Bool.false_eq_true,↓reduceIte,JFs_PublicLane.source,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,JFs_PublicComparisons.lane]
  simp only [Array.to_slice_mut,lift,bind_tc_ok]
  try simp (config := { zeta := true, iota := true }) only
  have lateCall : pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
      JFs_PublicValue.common.lane_transition (Array.to_slice (Array.repeat 1520#usize 0#u8))=
      ok (.Ok (),updated) := late
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let t ← g.getType
    Lean.logInfo m!"remaining constants: {t.getUsedConstants}"
  trace_state
  rw [lateCall]
  rfl

#print axioms source
end AspisR1.JFs_PublicValidation
