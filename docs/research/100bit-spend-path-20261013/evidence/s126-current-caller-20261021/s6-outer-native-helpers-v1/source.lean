import S6OuterNativeTotalCalleesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6OuterNativeHelpers

@[step] theorem common_spec (statement : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
    AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases statement <;> exact ⟨_,rfl,True.intro⟩

#print axioms common_spec

@[step] theorem transition_kind_spec (statement : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
    AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind statement ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases statement <;> exact ⟨_,rfl,True.intro⟩

#print axioms transition_kind_spec

@[step] theorem size_1520_spec : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES ⦃ result => result.val=1520 ⦄ := by
  unfold AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  step*

#print axioms size_1520_spec

@[step] theorem size_1664_spec : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET ⦃ result => result.val=1664 ⦄ := by
  unfold AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
  step*

#print axioms size_1664_spec

@[step] theorem map_LaneTransition {T : Type} (r : core.result.Result T AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) :
    AspisS6FullForestEncoderNamed.core.result.Result.map_err AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r with
  | Ok value => exact ⟨core.result.Result.Ok value,rfl,True.intro⟩
  | Err error => exact ⟨core.result.Result.Err (AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.LaneTransition error),rfl,True.intro⟩

#print axioms map_LaneTransition

@[step] theorem map_Payment {T : Type} (r : core.result.Result T AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    AspisS6FullForestEncoderNamed.core.result.Result.map_err AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r with
  | Ok value => exact ⟨core.result.Result.Ok value,rfl,True.intro⟩
  | Err error => exact ⟨core.result.Result.Err (AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Payment error),rfl,True.intro⟩

#print axioms map_Payment

end AspisS6OuterNativeHelpers
