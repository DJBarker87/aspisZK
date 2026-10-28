import R1Z.PV_RunJoin_DecoderStage829
import R1Z.PV_RunJoin_CodecContinuationBase30
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_CodecStage12Continuation30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CodecStage8Continuation30
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_CodecContinuationBase30

/-- An operational path with the actual returned snapshot passed to post.
It contains no whole decoder call or decoder-success premise. -/
def Path (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 : Array U32 8#usize) (post : PoolV1PairLiveSnapshotV1 → Prop) : Prop :=
  ∃ s13, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 416#usize, «end» := 448#usize }) = ok s13 ∧
  ∃ r27, (core.array.TryFromSharedArraySlice.try_from 32#usize s13) = ok r27 ∧
  ∃ a10, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r27) = ok a10 ∧
  ∃ r28, (atomic_statement.decode_digest_canonical a10) = ok r28 ∧
  ∃ r29, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r28 ()) = ok r29 ∧
  ∃ cf9, (core.result.Result.Insts.CoreOpsTry.branch r29) = ok cf9 ∧
  match cf9 with
  | core.ops.control_flow.ControlFlow.Continue val9 =>
    ∃ s14, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 448#usize, «end» := 480#usize }) = ok s14 ∧
    ∃ r30, (core.array.TryFromSharedArraySlice.try_from 32#usize s14) = ok r30 ∧
    ∃ a11, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r30) = ok a11 ∧
    ∃ r31, (atomic_statement.decode_digest_canonical a11) = ok r31 ∧
    ∃ r32, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r31 ()) = ok r32 ∧
    ∃ cf10, (core.result.Result.Insts.CoreOpsTry.branch r32) = ok cf10 ∧
    match cf10 with
    | core.ops.control_flow.ControlFlow.Continue val10 =>
      ∃ s15, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 480#usize, «end» := 512#usize }) = ok s15 ∧
      ∃ r33, (core.array.TryFromSharedArraySlice.try_from 32#usize s15) = ok r33 ∧
      ∃ a12, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r33) = ok a12 ∧
      ∃ r34, (atomic_statement.decode_digest_canonical a12) = ok r34 ∧
      ∃ r35, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r34 ()) = ok r35 ∧
      ∃ cf11, (core.result.Result.Insts.CoreOpsTry.branch r35) = ok cf11 ∧
      match cf11 with
      | core.ops.control_flow.ControlFlow.Continue val11 =>
        ∃ s16, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 512#usize, «end» := 544#usize }) = ok s16 ∧
        ∃ r36, (core.array.TryFromSharedArraySlice.try_from 32#usize s16) = ok r36 ∧
        ∃ a13, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r36) = ok a13 ∧
        ∃ r37, (atomic_statement.decode_digest_canonical a13) = ok r37 ∧
        ∃ r38, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r37 ()) = ok r38 ∧
        ∃ cf12, (core.result.Result.Insts.CoreOpsTry.branch r38) = ok cf12 ∧
        match cf12 with
        | core.ops.control_flow.ControlFlow.Continue val12 =>
          PV_RunJoin_CodecStage12Continuation30.Path bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 post
        | core.ops.control_flow.ControlFlow.Break residual => False
      | core.ops.control_flow.ControlFlow.Break residual => False
    | core.ops.control_flow.ControlFlow.Break residual => False
  | core.ops.control_flow.ControlFlow.Break residual => False

theorem path_wp (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 : Array U32 8#usize) (post : PoolV1PairLiveSnapshotV1 → Prop) :
    wp (PV_RunJoin_DecoderStage829.run bytes val val1 val2 val3 val4 val5 val6 val7 val8) (accepts post) ↔ Path bytes val val1 val2 val3 val4 val5 val6 val7 val8 post := by
  unfold PV_RunJoin_DecoderStage829.run Path
  simp only [bind_wp,ite_wp,ok_wp,accepts,residual_accepts,PV_RunJoin_CodecStage12Continuation30.path_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,accepts,residual_accepts,PV_RunJoin_CodecStage12Continuation30.path_wp])
#print axioms path_wp
end R1Z.PV_RunJoin_CodecStage8Continuation30
