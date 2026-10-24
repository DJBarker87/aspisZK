import S6OuterNativeHelpersV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6OuterNativeEncodeTotal
open AspisS6OuterNativeOps

private theorem array_slice_length {T : Type} {N : Usize} (value : Array T N) :
    (Array.to_slice value).length=N.val := value.property

@[step] theorem source_spec
    (statement : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
    AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 nativeOps statement ⦃ _ => True ⦄ := by
  unfold AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1
    AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.MASTER_OFFSET AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET
  step*
  all_goals (simp_all only [array_slice_length] <;> scalar_tac)

theorem encode_total (statement : AspisS6OuterNativeInstalled.Statement) :
    ∃ result, AspisS6OuterNativeInstalled.encode statement=ok result := by
  obtain ⟨result,run,_⟩ := spec_imp_exists
    (source_spec (AspisS6OuterCarrierBridge.fromPoolV1PairForestTerminalStatementV1 statement))
  unfold AspisS6OuterNativeInstalled.encode
  rw [run]
  exact ⟨_,rfl⟩

#print axioms source_spec
#print axioms encode_total
end AspisS6OuterNativeEncodeTotal
