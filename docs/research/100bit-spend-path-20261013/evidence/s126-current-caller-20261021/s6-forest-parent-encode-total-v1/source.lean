import S6ForestParentValidatorTotalV1
import S6SliceFrameLengthV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6ForestParent.Total
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_forest_terminal

@[step] theorem payment_offset_spec : PAYMENT_STATEMENT_OFFSET
    ⦃ result => result.val=1664 ⦄ := by
  unfold PAYMENT_STATEMENT_OFFSET LATE_STATEMENT_OFFSET
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  step*

@[step] theorem kind_spec (statement : PoolV1PairForestTerminalStatementV1) :
    PoolV1PairForestTerminalStatementV1.transition_kind statement
      ⦃ kind => 0 ≤ (read_discriminant kind : Isize).val ∧
        (read_discriminant kind : Isize).val ≤ 1 ⦄ := by
  apply exists_imp_spec
  cases statement <;> exact ⟨_,rfl,by decide⟩

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := a.property

/-- TOTAL complete 1880-byte encoder reference for both native statement
variants, including validator and child errors; no child-success premises. -/
@[step] theorem encode_spec (statement : PoolV1PairForestTerminalStatementV1) :
    encode statement ⦃ _ => True ⦄ := by
  unfold encode encode_pool_v1_pair_forest_terminal_statement_v1
    MASTER_OFFSET CHECKPOINT_ACCOUNT_OFFSET SELECTED_LANE_ACCOUNT_OFFSET
    CHECKPOINT_SEQUENCE_OFFSET HISTORICAL_ANCHOR_OFFSET LATE_STATEMENT_OFFSET
    POOL_V1_PAIR_FOREST_TERMINAL_VERSION
    aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> scalar_tac)

theorem encode_total (statement : PoolV1PairForestTerminalStatementV1) :
    ∃ result, encode statement=ok result := by
  obtain ⟨result,h,_⟩ := spec_imp_exists (encode_spec statement)
  exact ⟨result,h⟩

#print axioms payment_offset_spec
#print axioms kind_spec
#print axioms encode_total
end AspisS6ForestParent.Total
