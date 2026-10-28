import R1Z.PV_RunJoin_DecoderStage1629
import R1Z.PV_RunJoin_CodecContinuationBase30
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_CodecStage20Continuation30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CodecStage16Continuation30
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_CodecContinuationBase30

/-- An operational path with the actual returned snapshot passed to post.
It contains no whole decoder call or decoder-success premise. -/
def Path (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array U32 8#usize) (post : PoolV1PairLiveSnapshotV1 → Prop) : Prop :=
  ∃ s21, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 672#usize, «end» := 704#usize }) = ok s21 ∧
  ∃ r51, (core.array.TryFromSharedArraySlice.try_from 32#usize s21) = ok r51 ∧
  ∃ a18, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r51) = ok a18 ∧
  ∃ r52, (atomic_statement.decode_digest_canonical a18) = ok r52 ∧
  ∃ r53, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r52 ()) = ok r53 ∧
  ∃ cf17, (core.result.Result.Insts.CoreOpsTry.branch r53) = ok cf17 ∧
  match cf17 with
  | core.ops.control_flow.ControlFlow.Continue val17 =>
    ∃ s22, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 704#usize, «end» := 736#usize }) = ok s22 ∧
    ∃ r54, (core.array.TryFromSharedArraySlice.try_from 32#usize s22) = ok r54 ∧
    ∃ a19, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r54) = ok a19 ∧
    ∃ r55, (atomic_statement.decode_digest_canonical a19) = ok r55 ∧
    ∃ r56, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r55 ()) = ok r56 ∧
    ∃ cf18, (core.result.Result.Insts.CoreOpsTry.branch r56) = ok cf18 ∧
    match cf18 with
    | core.ops.control_flow.ControlFlow.Continue val18 =>
      ∃ s23, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 736#usize, «end» := 768#usize }) = ok s23 ∧
      ∃ r57, (core.array.TryFromSharedArraySlice.try_from 32#usize s23) = ok r57 ∧
      ∃ a20, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r57) = ok a20 ∧
      ∃ r58, (atomic_statement.decode_digest_canonical a20) = ok r58 ∧
      ∃ r59, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r58 ()) = ok r59 ∧
      ∃ cf19, (core.result.Result.Insts.CoreOpsTry.branch r59) = ok cf19 ∧
      match cf19 with
      | core.ops.control_flow.ControlFlow.Continue val19 =>
        ∃ s24, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 768#usize, «end» := 800#usize }) = ok s24 ∧
        ∃ r60, (core.array.TryFromSharedArraySlice.try_from 32#usize s24) = ok r60 ∧
        ∃ a21, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r60) = ok a21 ∧
        ∃ r61, (atomic_statement.decode_digest_canonical a21) = ok r61 ∧
        ∃ r62, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r61 ()) = ok r62 ∧
        ∃ cf20, (core.result.Result.Insts.CoreOpsTry.branch r62) = ok cf20 ∧
        match cf20 with
        | core.ops.control_flow.ControlFlow.Continue val20 =>
          PV_RunJoin_CodecStage20Continuation30.Path bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 post
        | core.ops.control_flow.ControlFlow.Break residual => False
      | core.ops.control_flow.ControlFlow.Break residual => False
    | core.ops.control_flow.ControlFlow.Break residual => False
  | core.ops.control_flow.ControlFlow.Break residual => False

theorem path_wp (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array U32 8#usize) (post : PoolV1PairLiveSnapshotV1 → Prop) :
    wp (PV_RunJoin_DecoderStage1629.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16) (accepts post) ↔ Path bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 post := by
  unfold PV_RunJoin_DecoderStage1629.run Path
  simp only [bind_wp,ite_wp,ok_wp,accepts,residual_accepts,PV_RunJoin_CodecStage20Continuation30.path_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,accepts,residual_accepts,PV_RunJoin_CodecStage20Continuation30.path_wp])
#print axioms path_wp
end R1Z.PV_RunJoin_CodecStage16Continuation30
