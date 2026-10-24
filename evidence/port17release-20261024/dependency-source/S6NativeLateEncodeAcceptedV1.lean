import S6NativeLateAcceptedValidityV1
import S6NativeLateChildEncodeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateEncodeAccepted
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeLateDecoderSplit.Frames

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := a.property

theorem encode_valid_spec (statement : PoolV1PairLatePublicStatementV1)
    (output : Slice U8) (size : output.length=1520)
    (snapshot_validated : validate_pool_v1_pair_live_snapshot_v1 statement.live_snapshot=ok (core.result.Result.Ok ()))
    (afterstate_validated : pool_v1.pair_terminal.validate_verified_afterstate statement.candidate_afterstate=ok (core.result.Result.Ok ()))
    (checked : U64.checked_add statement.live_snapshot.next_pair_index 1#u64=some statement.candidate_afterstate.next_pair_index) :
    encode_pool_v1_pair_late_public_statement_v1 statement output
      ⦃ result => result.1=core.result.Result.Ok () ∧ result.2.length=1520 ⦄ := by
  unfold encode_pool_v1_pair_late_public_statement_v1
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEq.ne.trait_default
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    AspisS6NativeSliceFrame.setSlice_length,List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> first | scalar_tac | step*)
  all_goals first
    | (have good := r3_post _ rfl; rw [good] at cf1_post; cases cf1_post)
    | (have good := r1_post () trivial; rw [good] at cf_post; cases cf_post)

#print axioms encode_valid_spec
end AspisS6NativeLateEncodeAccepted
