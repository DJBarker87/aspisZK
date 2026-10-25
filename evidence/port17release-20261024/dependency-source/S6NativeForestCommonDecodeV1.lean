import S6NativeForestDecodeHelpersV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeForestDecode
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

def common_frame (bytes : Slice U8) (common : PoolV1PairForestTerminalCommonV1) : Prop :=
  (∃ raw : Array U8 1880#usize, raw.val=bytes.val ∧ common.output_lane=raw.val[7]'(by rw [raw.property]; decide)) ∧
  common.master_account.val=List.slice 8 40 bytes.val ∧
  common.checkpoint_account.val=List.slice 40 72 bytes.val ∧
  common.selected_lane_account.val=List.slice 72 104 bytes.val ∧
  (core.num.U64.to_le_bytes common.checkpoint_sequence).val=List.slice 104 112 bytes.val ∧
  (∃ encoded : Array U8 32#usize, atomic_statement.encode_digest_canonical common.historical_global_anchor=ok encoded ∧
    encoded.val=List.slice 112 144 bytes.val) ∧
  (∃ late_bytes : Slice U8, late_bytes.val=List.slice 144 1664 bytes.val ∧
    pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1 late_bytes=
      ok (core.result.Result.Ok common.lane_transition))

@[step] theorem common_spec (bytes : Slice U8) (size : bytes.length=1880) :
    decode_terminal_common_boxed_v1 bytes ⦃ result => ∀ common,
      result=core.result.Result.Ok common → common_frame bytes common ⦄ := by
  unfold decode_terminal_common_boxed_v1 MASTER_OFFSET CHECKPOINT_ACCOUNT_OFFSET SELECTED_LANE_ACCOUNT_OFFSET
    CHECKPOINT_SEQUENCE_OFFSET HISTORICAL_ANCHOR_OFFSET LATE_STATEMENT_OFFSET
  step*
  all_goals (intro common accepted; cases accepted)
  all_goals (have hlen : bytes.val.length=1880 := size)
  all_goals (unfold common_frame)
  all_goals (refine ⟨⟨⟨bytes.val,hlen⟩,rfl,?_⟩,?_,?_,?_,?_,?_,⟨s1,?_,?_⟩⟩)
  all_goals (simp_all [AspisS6NativeDigestEncodeSourceEq.encode_eq,AspisS6ByteInverse.u64_to_from,List.slice])

  all_goals (refine ⟨AspisR1.S2K.DigestBytes.bytes val1,?_,?_⟩)
  all_goals first
    | (rw [←AspisS6NativeDigestEncodeSourceEq.encode_eq]; exact AspisR1.S2K.DigestBytes.exact val1)
    | exact (AspisS6NativeAfterstateEncoderReuse.native_digest_bytes val1).trans r2_post

theorem common_total (bytes : Slice U8) (size : bytes.length=1880) :
    ∃ result,decode_terminal_common_boxed_v1 bytes=ok result := by
  obtain ⟨result,run,_⟩ := spec_imp_exists (common_spec bytes size)
  exact ⟨result,run⟩

#print axioms common_spec
#print axioms common_total
end AspisS6NativeForestDecode
