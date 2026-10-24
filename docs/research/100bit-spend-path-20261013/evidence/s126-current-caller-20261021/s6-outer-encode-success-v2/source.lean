import S6OuterAcceptedCalleesV1
import S6OuterNativeEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6OuterEncodeSuccess
open AspisS6OuterNativeOps
open AspisS6FullForestEncoderNamed.aspis_statement.pool_v1

@[step] theorem validate_spec (value : pair_forest_terminal.PoolV1PairForestTerminalStatementV1)
    (ready : nativeOps.validate value=ok (.Ok ())) :
    nativeOps.validate value ⦃ result => result=core.result.Result.Ok () ⦄ := by
  rw [ready,WP.spec_ok]

@[step] theorem transfer_spec (value : payment_relation.PoolV1PrivateTransferPublicV1)
    (ready : ∃ encoded, nativeOps.transfer value=ok (.Ok encoded)) :
    nativeOps.transfer value ⦃ result => ∃ encoded, result=core.result.Result.Ok encoded ⦄ := by
  obtain ⟨encoded,run⟩ := ready
  rw [run,WP.spec_ok]
  exact ⟨encoded,rfl⟩

@[step] theorem withdrawal_spec (value : payment_relation.PoolV1WithdrawalPublicV1)
    (ready : ∃ encoded, nativeOps.withdrawal value=ok (.Ok encoded)) :
    nativeOps.withdrawal value ⦃ result => ∃ encoded, result=core.result.Result.Ok encoded ⦄ := by
  obtain ⟨encoded,run⟩ := ready
  rw [run,WP.spec_ok]
  exact ⟨encoded,rfl⟩

def late_ready (value : pair_tree_profile.PoolV1PairLatePublicStatementV1) : Prop :=
  ∀ output : Slice U8, output.length=1520 → ∃ updated,
    nativeOps.late value output=ok (.Ok (),updated) ∧ updated.length=1520

@[step] theorem late_spec (value : pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (output : Slice U8) (size : output.length=1520) (ready : late_ready value) :
    nativeOps.late value output ⦃ result => result.1=core.result.Result.Ok () ∧ result.2.length=1520 ⦄ := by
  obtain ⟨updated,run,len⟩ := ready output size
  rw [run,WP.spec_ok]
  exact ⟨rfl,len⟩

@[step] theorem branch_graph {T E : Type} (r : core.result.Result T E) :
    core.result.Result.Insts.CoreOpsTry.branch r
      ⦃ cf => core.result.Result.Insts.CoreOpsTry.branch r=ok cf ⦄ := by
  apply exists_imp_spec
  cases r <;> exact ⟨_,rfl,rfl⟩

@[step] theorem map_LaneTransition {T : Type} (r : core.result.Result T AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) :
    AspisS6FullForestEncoderNamed.core.result.Result.map_err AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1 r () ⦃ result => ∀ value, r=core.result.Result.Ok value → result=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r with
  | Ok value => exact ⟨core.result.Result.Ok value,rfl,by intro v eq; cases eq; rfl⟩
  | Err error => exact ⟨core.result.Result.Err (AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.LaneTransition error),rfl,by intro v eq; cases eq⟩


@[step] theorem map_Payment {T : Type} (r : core.result.Result T AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    AspisS6FullForestEncoderNamed.core.result.Result.map_err AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r () ⦃ result => ∀ value, r=core.result.Result.Ok value → result=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r with
  | Ok value => exact ⟨core.result.Result.Ok value,rfl,by intro v eq; cases eq; rfl⟩
  | Err error => exact ⟨core.result.Result.Err (AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Payment error),rfl,by intro v eq; cases eq⟩


private theorem array_slice_length {T : Type} {N : Usize} (value : Array T N) :
    (Array.to_slice value).length=N.val := value.property

theorem private_success
    (common : pair_forest_terminal.PoolV1PairForestTerminalCommonV1)
    (payload : payment_relation.PoolV1PrivateTransferPublicV1)
    (valid : nativeOps.validate (.PrivateTransfer common payload)=ok (.Ok ()))
    (late : late_ready common.lane_transition)
    (pay : ∃ encoded, nativeOps.transfer payload=ok (.Ok encoded)) :
    pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 nativeOps (.PrivateTransfer common payload)
      ⦃ result => ∃ encoded, result=core.result.Result.Ok encoded ⦄ := by
  unfold pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1
    pair_forest_terminal.MASTER_OFFSET pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET
    pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET
    pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET pair_forest_terminal.LATE_STATEMENT_OFFSET
  simp only [pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common,
    pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind]
  step*
  all_goals (simp_all only [array_slice_length] <;> first | scalar_tac | step*)

  all_goals first
    | (have good := r4_post _ r3_post; rw [good] at cf2_post; cases cf2_post)
    | (have good := r2_post () trivial; rw [good] at cf1_post; cases cf1_post)
    | cases cf_post

#print axioms validate_spec
#print axioms transfer_spec
#print axioms withdrawal_spec
#print axioms late_spec
#print axioms branch_graph
#print axioms map_LaneTransition
#print axioms map_Payment
#print axioms private_success
end AspisS6OuterEncodeSuccess
