import RPz7_S6NativeLateHeaderWritesV1
import RPz7_S6NativeLateChildEncodeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateEncoderContents
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeLateDecoderSplit.Frames

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := a.property

theorem encode_contents_spec (statement : PoolV1PairLatePublicStatementV1)
    (output : Slice U8) (size : output.length=1520)
    (snapshot_validated : validate_pool_v1_pair_live_snapshot_v1 statement.live_snapshot=ok (core.result.Result.Ok ()))
    (afterstate_validated : pool_v1.pair_terminal.validate_verified_afterstate statement.candidate_afterstate=ok (core.result.Result.Ok ()))
    (checked : U64.checked_add statement.live_snapshot.next_pair_index 1#u64=some statement.candidate_afterstate.next_pair_index) :
    encode_pool_v1_pair_late_public_statement_v1 statement output
      ⦃ result => result.1=core.result.Result.Ok () ∧
        ∃ snapshot_input snapshot_output : Slice U8, ∃ afterstate_output : Array U8 688#usize,
          encode_pool_v1_pair_live_snapshot_v1 statement.live_snapshot snapshot_input=
            ok (core.result.Result.Ok (),snapshot_output) ∧
          pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 statement.candidate_afterstate=
            ok (core.result.Result.Ok afterstate_output) ∧
          snapshot_output.length=800 ∧
          result.2.val=(AspisS6NativeLateHeaderLayout.header_bytes++snapshot_output.val)++afterstate_output.val ⦄ := by
  unfold encode_pool_v1_pair_late_public_statement_v1
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEq.ne.trait_default
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    AspisS6NativeSliceFrame.setSlice_length,List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> first | scalar_tac | step*)
  all_goals try (solve
    | (have good := r3_post _ rfl; rw [good] at cf1_post; cases cf1_post)
    | (have good := r1_post () trivial; rw [good] at cf_post; cases cf_post))
  all_goals (have good := r3_post _ rfl)
  all_goals (have same : val=r2 := by rw [good] at cf1_post; cases cf1_post; rfl)
  all_goals (refine ⟨s15,s16,r2,r_post2,rfl,r_post3,?_⟩)
  all_goals (
    have a_bytes : a.val=(core.num.U16.to_le_bytes 32#u16).val := by
      simpa only [core.num.U16.to_le_bytes,AspisS6NativeLateHeaderLayout.cast16_32] using a_post)
  all_goals (
    have a1_bytes : a1.val=(core.num.U32.to_le_bytes 800#u32).val := by
      simpa only [core.num.U32.to_le_bytes,AspisS6NativeLateHeaderLayout.cast32_800] using a1_post)
  all_goals (
    have a2_bytes : a2.val=(core.num.U32.to_le_bytes 688#u32).val := by
      simpa only [core.num.U32.to_le_bytes,AspisS6NativeLateHeaderLayout.cast32_688] using a2_post)
  all_goals (
    have a3_bytes : a3.val=(core.num.U32.to_le_bytes 1520#u32).val := by
      simpa only [core.num.U32.to_le_bytes,AspisS6NativeLateHeaderLayout.cast32_1520] using a3_post)
  all_goals (simp only [Slice.setSlice!,Array.to_slice,a_bytes,a1_bytes,a2_bytes,a3_bytes,same])
  all_goals (exact AspisS6NativeLateHeaderLayout.assembled s16.val r2.val r_post3 r2.property)

#print axioms encode_contents_spec
end AspisS6NativeLateEncoderContents
