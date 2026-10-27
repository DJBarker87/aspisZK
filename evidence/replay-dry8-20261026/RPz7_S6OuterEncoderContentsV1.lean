import RPz7_S6OuterEncodeFromDecodeV1
import RPz7_S6OuterByteLayoutV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6OuterEncoderContents
open AspisS6OuterNativeOps AspisS6OuterEncodeSuccess
open AspisS6FullForestEncoderNamed.aspis_statement.pool_v1

@[step] theorem transfer_spec (value : payment_relation.PoolV1PrivateTransferPublicV1)
    (ready : ∃ encoded, nativeOps.transfer value=ok (.Ok encoded)) :
    nativeOps.transfer value ⦃ result => ∃ encoded, result=core.result.Result.Ok encoded ∧ nativeOps.transfer value=ok (.Ok encoded) ⦄ := by
  obtain ⟨encoded,run⟩ := ready
  rw [run,WP.spec_ok]
  exact ⟨encoded,rfl,rfl⟩

@[step] theorem withdrawal_spec (value : payment_relation.PoolV1WithdrawalPublicV1)
    (ready : ∃ encoded, nativeOps.withdrawal value=ok (.Ok encoded)) :
    nativeOps.withdrawal value ⦃ result => ∃ encoded, result=core.result.Result.Ok encoded ∧ nativeOps.withdrawal value=ok (.Ok encoded) ⦄ := by
  obtain ⟨encoded,run⟩ := ready
  rw [run,WP.spec_ok]
  exact ⟨encoded,rfl,rfl⟩

@[step] theorem late_spec (value : pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (output : Slice U8) (size : output.length=1520) (ready : late_ready value) :
    nativeOps.late value output ⦃ result => result.1=core.result.Result.Ok () ∧ result.2.length=1520 ∧ nativeOps.late value output=ok result ⦄ := by
  obtain ⟨updated,run,len⟩ := ready output size
  rw [run,WP.spec_ok]
  exact ⟨rfl,len,rfl⟩

@[step] theorem digest_spec (digest : Array U32 8#usize) :
    nativeOps.digest digest ⦃ result => result.val=AspisS6SourceCodec.DigestContents.chunks digest ⦄ := by
  exact AspisS6NativeSnapshotEncodeTotal.digest_spec digest

abbrev common_prefix := AspisS6OuterByteLayout.common_prefix

private theorem array_slice_length {T : Type} {N : Usize} (value : Array T N) :
    (Array.to_slice value).length=N.val := value.property

theorem private_contents
    (common : pair_forest_terminal.PoolV1PairForestTerminalCommonV1)
    (payload : payment_relation.PoolV1PrivateTransferPublicV1)
    (valid : nativeOps.validate (.PrivateTransfer common payload)=ok (.Ok ()))
    (late : late_ready common.lane_transition)
    (pay : ∃ encoded, nativeOps.transfer payload=ok (.Ok encoded)) :
    pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 nativeOps (.PrivateTransfer common payload)
      ⦃ result => ∃ encoded : Array U8 1880#usize, ∃ initial updated : Slice U8, ∃ payment : Array U8 216#usize,
        result=core.result.Result.Ok encoded ∧ initial.length=1520 ∧ updated.length=1520 ∧
        nativeOps.late common.lane_transition initial=ok (.Ok (),updated) ∧
        nativeOps.transfer payload=ok (.Ok payment) ∧
        encoded.val=(common_prefix common 1#u8++updated.val)++payment.val ⦄ := by
  unfold pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1
    pair_forest_terminal.MASTER_OFFSET pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET
    pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET
    pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET pair_forest_terminal.LATE_STATEMENT_OFFSET
  simp only [pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common,
    pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind]
  step*
  all_goals (simp_all only [array_slice_length] <;> first | scalar_tac | step*)
  all_goals try (solve
    | (have good := r4_post _ rfl; rw [good] at cf2_post; cases cf2_post)
    | (have good := r2_post () trivial; rw [good] at cf1_post; cases cf1_post)
    | cases cf_post)

  all_goals (have good := r4_post _ rfl)
  all_goals (have same : val=r3 := by rw [good] at cf2_post; cases cf2_post; rfl)
  all_goals (refine ⟨_,s18,s19,r3,rfl,by scalar_tac,r1_post2,r1_post3,rfl,?_⟩)
  all_goals (rw [s20_post3])
  all_goals (have cast_tag : UScalar.cast .U8 (read_discriminant historical_anchor.PoolV1TransitionKind.PrivateTransfer)=1#u8 := by rfl)
  all_goals (simp only [Aeneas.Std.Array.set_val_eq,s_post3,cast_tag])
  all_goals (simp only [Array.to_slice,Aeneas.Std.Array.repeat,same,a1_post])
  all_goals (have assembled := AspisS6OuterByteLayout.assembled common 1#u8 s19.val r3.val r1_post2 r3.property)
  all_goals (unfold AspisS6OuterByteLayout.prepared_header at assembled)
  all_goals (exact assembled)

theorem withdrawal_contents
    (common : pair_forest_terminal.PoolV1PairForestTerminalCommonV1)
    (payload : payment_relation.PoolV1WithdrawalPublicV1)
    (valid : nativeOps.validate (.Withdrawal common payload)=ok (.Ok ()))
    (late : late_ready common.lane_transition)
    (pay : ∃ encoded, nativeOps.withdrawal payload=ok (.Ok encoded)) :
    pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 nativeOps (.Withdrawal common payload)
      ⦃ result => ∃ encoded : Array U8 1880#usize, ∃ initial updated : Slice U8, ∃ payment : Array U8 216#usize,
        result=core.result.Result.Ok encoded ∧ initial.length=1520 ∧ updated.length=1520 ∧
        nativeOps.late common.lane_transition initial=ok (.Ok (),updated) ∧
        nativeOps.withdrawal payload=ok (.Ok payment) ∧
        encoded.val=(common_prefix common 2#u8++updated.val)++payment.val ⦄ := by
  unfold pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1
    pair_forest_terminal.MASTER_OFFSET pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET
    pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET
    pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET pair_forest_terminal.LATE_STATEMENT_OFFSET
  simp only [pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common,
    pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind]
  step*
  all_goals (simp_all only [array_slice_length] <;> first | scalar_tac | step*)
  all_goals try (solve
    | (have good := r4_post _ rfl; rw [good] at cf2_post; cases cf2_post)
    | (have good := r2_post () trivial; rw [good] at cf1_post; cases cf1_post)
    | cases cf_post)

  all_goals (have good := r4_post _ rfl)
  all_goals (have same : val=r3 := by rw [good] at cf2_post; cases cf2_post; rfl)
  all_goals (refine ⟨_,s18,s19,r3,rfl,by scalar_tac,r1_post2,r1_post3,rfl,?_⟩)
  all_goals (rw [s20_post3])
  all_goals (have cast_tag : UScalar.cast .U8 (read_discriminant historical_anchor.PoolV1TransitionKind.Withdrawal)=2#u8 := by rfl)
  all_goals (simp only [Aeneas.Std.Array.set_val_eq,s_post3,cast_tag])
  all_goals (simp only [Array.to_slice,Aeneas.Std.Array.repeat,same,a1_post])
  all_goals (have assembled := AspisS6OuterByteLayout.assembled common 2#u8 s19.val r3.val r1_post2 r3.property)
  all_goals (unfold AspisS6OuterByteLayout.prepared_header at assembled)
  all_goals (exact assembled)

#print axioms transfer_spec
#print axioms withdrawal_spec
#print axioms late_spec
#print axioms digest_spec
#print axioms private_contents
#print axioms withdrawal_contents
end AspisS6OuterEncoderContents
