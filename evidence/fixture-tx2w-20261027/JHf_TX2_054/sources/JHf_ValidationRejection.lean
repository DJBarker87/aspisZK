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
  have zm : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      JHf_ReconstructedStatement.common.master_account (Array.repeat 32#usize 0#u8)=ok false :=
    JFs_PublicValue.master_nonzero
  have zc : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      JHf_ReconstructedStatement.common.checkpoint_account (Array.repeat 32#usize 0#u8)=ok false :=
    JFs_PublicValue.checkpoint_nonzero
  have zl : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      JHf_ReconstructedStatement.common.selected_lane_account (Array.repeat 32#usize 0#u8)=ok false :=
    JFs_PublicValue.lane_nonzero
  have lane : ¬(core.convert.num.FromUsizeU8.from JHf_ReconstructedStatement.common.output_lane >=
      pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT) := JFs_PublicComparisons.lane_bound
  have pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      JFs_PaymentValue.common.pool JHf_ReconstructedStatement.common.master_account=ok false :=
    JFs_PublicComparisons.pool
  have domain : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      JFs_PaymentValue.common.deployment_domain
      JHf_ReconstructedStatement.common.lane_transition.live_snapshot.deployment_domain=ok true :=
    JHf_ReconstructedStatement.domain_compare
  dsimp only [JHf_ReconstructedStatement.value] at publicCall
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
  rw [common]
  simp only [bind_tc_ok,zm,zc,zl,Bool.false_eq_true,↓reduceIte,lift,lane]
  rw [show JHf_ReconstructedStatement.value=.PrivateTransfer JHf_ReconstructedStatement.common JFs_PaymentValue.value from rfl]
  simp only [payment,bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  rw [publicCall]
  dsimp only
  simp only [bind_tc_ok,pool,domain,
    Bool.false_eq_true,↓reduceIte]
#print axioms source
end AspisR1.JHf_ValidationRejection
