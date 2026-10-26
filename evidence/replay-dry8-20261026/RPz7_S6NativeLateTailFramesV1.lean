import RPz7_S6NativeLateDecoderSplitV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateDecoderSplit.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def reserved_frame (raw : Array U8 1520#usize) : Prop :=
  raw.val[24]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[25]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[26]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[27]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[28]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[29]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[30]'(by rw [raw.property]; decide)=0#u8 ∧
  raw.val[31]'(by rw [raw.property]; decide)=0#u8

def body_frame (bytes : Slice U8) (statement : PoolV1PairLatePublicStatementV1) : Prop :=
  (∃ snapshot_input afterstate_input : Slice U8,
    snapshot_input.val=List.slice 32 832 bytes.val ∧
    afterstate_input.val=bytes.val.drop 832 ∧
    decode_pool_v1_pair_live_snapshot_v1 snapshot_input=ok (core.result.Result.Ok statement.live_snapshot) ∧
    pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 afterstate_input=
      ok (core.result.Result.Ok statement.candidate_afterstate)) ∧
  U64.checked_add statement.live_snapshot.next_pair_index 1#u64=some statement.candidate_afterstate.next_pair_index

def tail_frame (bytes : Slice U8) (statement : PoolV1PairLatePublicStatementV1) : Prop :=
  (∃ raw : Array U8 1520#usize, raw.val=bytes.val ∧ reserved_frame raw) ∧ body_frame bytes statement

@[step] theorem checked_add_graph (a b : U64) :
    lift (U64.checked_add a b) ⦃ result => result=U64.checked_add a b ⦄ := by
  apply exists_imp_spec
  exact ⟨_,rfl,rfl⟩

@[step] theorem tail_frames (bytes : Slice U8) (size : bytes.length=1520) : decode_tail bytes
    ⦃ result => ∀ statement, result=core.result.Result.Ok statement → tail_frame bytes statement ⦄ := by
  unfold decode_tail POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    core.cmp.PartialEq.ne.trait_default core.option.Option.Insts.CoreCmpPartialEqOption
  step*
  all_goals (simp_all only [tail_frame,body_frame])
  all_goals (intro statement accepted; cases accepted)
  all_goals (have hlen : bytes.val.length=1520 := size)
  all_goals (refine ⟨⟨⟨bytes.val,hlen⟩,rfl,?_⟩,⟨s6,s7,?_,?_,?_,?_⟩,?_⟩)
  all_goals (simp_all [reserved_frame,List.slice] <;> (repeat' constructor))
  all_goals scalar_tac

#print axioms checked_add_graph
#print axioms tail_frames
end AspisS6NativeLateDecoderSplit.Frames
