import S6NativeLateTailFramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateDecoderSplit.Frames
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
  reserved_frame raw

def full_frame (bytes : Slice U8) (statement : PoolV1PairLatePublicStatementV1) : Prop :=
  (∃ raw : Array U8 1520#usize, raw.val=bytes.val ∧ header_frame raw) ∧ body_frame bytes statement

@[step] theorem decode_frames (bytes : Slice U8) : decode bytes
    ⦃ result => ∀ statement, result=core.result.Result.Ok statement → full_frame bytes statement ⦄ := by
  unfold decode POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals step*
  all_goals (simp_all only [full_frame])
  all_goals (have later := result_post1 _ rfl)
  all_goals (rcases later with ⟨⟨raw,rawbytes,reserved⟩,body⟩)
  all_goals (have w16 := congrArg Subtype.val (AspisS6NativeLateWordCast.word16_32 a (by assumption)))
  all_goals (have w32a := congrArg Subtype.val (AspisS6NativeLateWordCast.word32_800 a1 (by assumption)))
  all_goals (have w32b := congrArg Subtype.val (AspisS6NativeLateWordCast.word32_688 a2 (by assumption)))
  all_goals (have w32c := congrArg Subtype.val (AspisS6NativeLateWordCast.word32_1520 a3 (by assumption)))
  all_goals (refine ⟨⟨raw,rawbytes,?_⟩,body⟩)
  all_goals (unfold header_frame; refine ⟨?_,?_,?_,?_,?_,?_,?_,reserved⟩)
  all_goals (rw [rawbytes])
  all_goals (simp_all [List.slice])
  all_goals first
    | scalar_tac
    | (have hm : List.take 8 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val=POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val := by
         have h := List.take_length (l := POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val)
         simpa [POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.property] using h
       exact s_post1.symm.trans hm)

#print axioms decode_frames
end AspisS6NativeLateDecoderSplit.Frames
