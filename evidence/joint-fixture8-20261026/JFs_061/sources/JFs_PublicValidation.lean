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
  simp only [bind_tc_ok,JFs_PublicComparisons.pool,JFs_PublicComparisons.domain,
    JFs_PublicComparisons.snapshot_pool,JFs_PublicComparisons.anchor,JFs_PublicComparisons.sequence,
    Bool.false_eq_true,↓reduceIte,JFs_PublicLane.source,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,JFs_PublicComparisons.lane]
  simp only [Array.to_slice_mut,lift,bind_tc_ok,late,core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch]

#print axioms source
end AspisR1.JFs_PublicValidation
