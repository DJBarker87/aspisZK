import S6NativeLateWordConstantsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def header_frame (raw : Array U8 1520#usize) : Prop :=
  List.slice 0 8 raw.val=POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val ∧
  raw.val[8]'(by rw [raw.property]; decide)=POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION ∧
  raw.val[9]'(by rw [raw.property]; decide)=POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT ∧
  (core.num.U16.to_le_bytes 32#u16).val=List.slice 10 12 raw.val ∧
  (core.num.U32.to_le_bytes 800#u32).val=List.slice 12 16 raw.val ∧
  (core.num.U32.to_le_bytes 688#u32).val=List.slice 16 20 raw.val ∧
  (core.num.U32.to_le_bytes 1520#u32).val=List.slice 20 24 raw.val ∧
  raw.val[24]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[25]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[26]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[27]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[28]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[29]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[30]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[31]'(by rw [raw.property]; decide)=0#u8

def full_frame (bytes : Slice U8) (statement : PoolV1PairLatePublicStatementV1) : Prop :=
  (∃ raw : Array U8 1520#usize, raw.val=bytes.val ∧ header_frame raw) ∧
  (∃ snapshot_input afterstate_input : Slice U8,
    snapshot_input.val=List.slice 32 832 bytes.val ∧
    afterstate_input.val=bytes.val.drop 832 ∧
    decode_pool_v1_pair_live_snapshot_v1 snapshot_input=ok (core.result.Result.Ok statement.live_snapshot) ∧
    pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 afterstate_input=
      ok (core.result.Result.Ok statement.candidate_afterstate)) ∧
  U64.checked_add statement.live_snapshot.next_pair_index 1#u64=some statement.candidate_afterstate.next_pair_index

@[step] theorem checked_add_graph (a b : U64) :
    lift (U64.checked_add a b) ⦃ result => result=U64.checked_add a b ⦄ := by
  apply exists_imp_spec
  exact ⟨_,rfl,rfl⟩

@[step] theorem decode_frames (bytes : Slice U8) : decode bytes
    ⦃ result => ∀ statement, result=core.result.Result.Ok statement → full_frame bytes statement ⦄ := by
  unfold decode POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
    core.option.Option.Insts.CoreCmpPartialEqOption
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals step*
  all_goals (simp_all only [full_frame])
  all_goals (intro statement accepted; cases accepted)
  all_goals (have hlen : bytes.val.length=1520 := by scalar_tac)
  all_goals (have w16 := congrArg Subtype.val (AspisS6NativeLateWordCast.word16_32 a (by assumption)))
  all_goals (have w32a := congrArg Subtype.val (AspisS6NativeLateWordCast.word32_800 a1 (by assumption)))
  all_goals (have w32b := congrArg Subtype.val (AspisS6NativeLateWordCast.word32_688 a2 (by assumption)))
  all_goals (have w32c := congrArg Subtype.val (AspisS6NativeLateWordCast.word32_1520 a3 (by assumption)))
  all_goals (refine ⟨⟨⟨bytes.val,hlen⟩,rfl,?_⟩,⟨s6,s7,?_,?_,?_,?_⟩,?_⟩)
  all_goals (simp_all [header_frame,List.slice] <;> (repeat' constructor))
  all_goals first
    | scalar_tac
    | (have hm : List.take 8 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val=POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val := by
         have h := List.take_length (l := POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val)
         simpa [POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.property] using h
       exact s_post1.symm.trans hm)

#print axioms checked_add_graph
#print axioms decode_frames
end AspisS6NativeLateDecoderFactored.Frames
