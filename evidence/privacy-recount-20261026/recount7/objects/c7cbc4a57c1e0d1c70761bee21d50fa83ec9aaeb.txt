import R1Z.PV_RunJoin_DecoderStage429
import R1Z.PV_RunJoin_CodecContinuationBase30
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_CodecStage8Continuation30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CodecStage4Continuation30
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_CodecContinuationBase30

/-- An operational path with the actual returned snapshot passed to post.
It contains no whole decoder call or decoder-success premise. -/
def Path (bytes : Slice U8) (val val1 val2 val3 val4 : Array U32 8#usize) (post : PoolV1PairLiveSnapshotV1 → Prop) : Prop :=
  ∃ s9, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 288#usize, «end» := 320#usize }) = ok s9 ∧
  ∃ r15, (core.array.TryFromSharedArraySlice.try_from 32#usize s9) = ok r15 ∧
  ∃ a6, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r15) = ok a6 ∧
  ∃ r16, (atomic_statement.decode_digest_canonical a6) = ok r16 ∧
  ∃ r17, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r16 ()) = ok r17 ∧
  ∃ cf5, (core.result.Result.Insts.CoreOpsTry.branch r17) = ok cf5 ∧
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue val5 =>
    ∃ s10, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 320#usize, «end» := 352#usize }) = ok s10 ∧
    ∃ r18, (core.array.TryFromSharedArraySlice.try_from 32#usize s10) = ok r18 ∧
    ∃ a7, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r18) = ok a7 ∧
    ∃ r19, (atomic_statement.decode_digest_canonical a7) = ok r19 ∧
    ∃ r20, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r19 ()) = ok r20 ∧
    ∃ cf6, (core.result.Result.Insts.CoreOpsTry.branch r20) = ok cf6 ∧
    match cf6 with
    | core.ops.control_flow.ControlFlow.Continue val6 =>
      ∃ s11, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 352#usize, «end» := 384#usize }) = ok s11 ∧
      ∃ r21, (core.array.TryFromSharedArraySlice.try_from 32#usize s11) = ok r21 ∧
      ∃ a8, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r21) = ok a8 ∧
      ∃ r22, (atomic_statement.decode_digest_canonical a8) = ok r22 ∧
      ∃ r23, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r22 ()) = ok r23 ∧
      ∃ cf7, (core.result.Result.Insts.CoreOpsTry.branch r23) = ok cf7 ∧
      match cf7 with
      | core.ops.control_flow.ControlFlow.Continue val7 =>
        ∃ s12, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 384#usize, «end» := 416#usize }) = ok s12 ∧
        ∃ r24, (core.array.TryFromSharedArraySlice.try_from 32#usize s12) = ok r24 ∧
        ∃ a9, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r24) = ok a9 ∧
        ∃ r25, (atomic_statement.decode_digest_canonical a9) = ok r25 ∧
        ∃ r26, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r25 ()) = ok r26 ∧
        ∃ cf8, (core.result.Result.Insts.CoreOpsTry.branch r26) = ok cf8 ∧
        match cf8 with
        | core.ops.control_flow.ControlFlow.Continue val8 =>
          PV_RunJoin_CodecStage8Continuation30.Path bytes val val1 val2 val3 val4 val5 val6 val7 val8 post
        | core.ops.control_flow.ControlFlow.Break residual => False
      | core.ops.control_flow.ControlFlow.Break residual => False
    | core.ops.control_flow.ControlFlow.Break residual => False
  | core.ops.control_flow.ControlFlow.Break residual => False

theorem path_wp (bytes : Slice U8) (val val1 val2 val3 val4 : Array U32 8#usize) (post : PoolV1PairLiveSnapshotV1 → Prop) :
    wp (PV_RunJoin_DecoderStage429.run bytes val val1 val2 val3 val4) (accepts post) ↔ Path bytes val val1 val2 val3 val4 post := by
  unfold PV_RunJoin_DecoderStage429.run Path
  simp only [bind_wp,ite_wp,ok_wp,accepts,residual_accepts,PV_RunJoin_CodecStage8Continuation30.path_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,accepts,residual_accepts,PV_RunJoin_CodecStage8Continuation30.path_wp])
#print axioms path_wp
end R1Z.PV_RunJoin_CodecStage4Continuation30
