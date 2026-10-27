import JHf_ReconstructedStatement
set_option autoImplicit false
namespace AspisR1.JHf_ValidationRejection
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
attribute [local irreducible] JHf_DomainBytes.master

theorem source : validate_pool_v1_pair_forest_terminal_statement_v1 JHf_ReconstructedStatement.value=
    ok (.Err .DeploymentBindingMismatch) := by
  obtain ⟨encoded,contents,payment⟩:=JFs_PublicEncoders.payment
  have common : PoolV1PairForestTerminalStatementV1.common JHf_ReconstructedStatement.value=
      ok JHf_ReconstructedStatement.common := rfl
  have publicCall : statement_public_common JHf_ReconstructedStatement.value=
      ok (JFs_PaymentValue.common.pool,JFs_PaymentValue.common.deployment_domain,
        JFs_PaymentValue.common.anchor_sequence,JFs_PaymentValue.common.anchor_root,
        JFs_PaymentValue.common.nullifier,JFs_PaymentValue.common.asset_id) := rfl
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
  rw [common]
  simp only [bind_tc_ok,JFs_PublicValue.master_nonzero,JFs_PublicValue.checkpoint_nonzero,
    JFs_PublicValue.lane_nonzero,Bool.false_eq_true,↓reduceIte,lift,JFs_PublicComparisons.lane_bound]
  rw [show JHf_ReconstructedStatement.value=.PrivateTransfer JHf_ReconstructedStatement.common JFs_PaymentValue.value from rfl]
  simp only [payment,bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  rw [publicCall]
  simp only [bind_tc_ok,JFs_PublicComparisons.pool,JHf_ReconstructedStatement.domain_compare,
    Bool.false_eq_true,↓reduceIte]
#print axioms source
end AspisR1.JHf_ValidationRejection
