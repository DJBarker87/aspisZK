import R1Z.PV_RunJoin_DecoderStage029
import R1Z.PV_RunJoin_CodecContinuationBase30
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_CodecStage4Continuation30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CodecStage0Continuation30
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_CodecContinuationBase30

/-- An operational path with the actual returned snapshot passed to post.
It contains no whole decoder call or decoder-success premise. -/
def Path (bytes : Slice U8) (val : Array U32 8#usize) (post : PoolV1PairLiveSnapshotV1 → Prop) : Prop :=
  ∃ s5, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 160#usize, «end» := 192#usize }) = ok s5 ∧
  ∃ r3, (core.array.TryFromSharedArraySlice.try_from 32#usize s5) = ok r3 ∧
  ∃ a2, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r3) = ok a2 ∧
  ∃ r4, (atomic_statement.decode_digest_canonical a2) = ok r4 ∧
  ∃ r5, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r4 ()) = ok r5 ∧
  ∃ cf1, (core.result.Result.Insts.CoreOpsTry.branch r5) = ok cf1 ∧
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    ∃ s6, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 192#usize, «end» := 224#usize }) = ok s6 ∧
    ∃ r6, (core.array.TryFromSharedArraySlice.try_from 32#usize s6) = ok r6 ∧
    ∃ a3, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r6) = ok a3 ∧
    ∃ r7, (atomic_statement.decode_digest_canonical a3) = ok r7 ∧
    ∃ r8, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r7 ()) = ok r8 ∧
    ∃ cf2, (core.result.Result.Insts.CoreOpsTry.branch r8) = ok cf2 ∧
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      ∃ s7, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 224#usize, «end» := 256#usize }) = ok s7 ∧
      ∃ r9, (core.array.TryFromSharedArraySlice.try_from 32#usize s7) = ok r9 ∧
      ∃ a4, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r9) = ok a4 ∧
      ∃ r10, (atomic_statement.decode_digest_canonical a4) = ok r10 ∧
      ∃ r11, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r10 ()) = ok r11 ∧
      ∃ cf3, (core.result.Result.Insts.CoreOpsTry.branch r11) = ok cf3 ∧
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val3 =>
        ∃ s8, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 256#usize, «end» := 288#usize }) = ok s8 ∧
        ∃ r12, (core.array.TryFromSharedArraySlice.try_from 32#usize s8) = ok r12 ∧
        ∃ a5, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r12) = ok a5 ∧
        ∃ r13, (atomic_statement.decode_digest_canonical a5) = ok r13 ∧
        ∃ r14, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r13 ()) = ok r14 ∧
        ∃ cf4, (core.result.Result.Insts.CoreOpsTry.branch r14) = ok cf4 ∧
        match cf4 with
        | core.ops.control_flow.ControlFlow.Continue val4 =>
          PV_RunJoin_CodecStage4Continuation30.Path bytes val val1 val2 val3 val4 post
        | core.ops.control_flow.ControlFlow.Break residual => False
      | core.ops.control_flow.ControlFlow.Break residual => False
    | core.ops.control_flow.ControlFlow.Break residual => False
  | core.ops.control_flow.ControlFlow.Break residual => False

theorem path_wp (bytes : Slice U8) (val : Array U32 8#usize) (post : PoolV1PairLiveSnapshotV1 → Prop) :
    wp (PV_RunJoin_DecoderStage029.run bytes val) (accepts post) ↔ Path bytes val post := by
  unfold PV_RunJoin_DecoderStage029.run Path
  simp only [bind_wp,ite_wp,ok_wp,accepts,residual_accepts,PV_RunJoin_CodecStage4Continuation30.path_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,accepts,residual_accepts,PV_RunJoin_CodecStage4Continuation30.path_wp])
#print axioms path_wp
end R1Z.PV_RunJoin_CodecStage0Continuation30
