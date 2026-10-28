import R1Z.PV_RunJoin_DecoderStage1229
import R1Z.PV_RunJoin_CodecContinuationBase30
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_CodecStage16Continuation30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CodecStage12Continuation30
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_CodecContinuationBase30

/-- An operational path with the actual returned snapshot passed to post.
It contains no whole decoder call or decoder-success premise. -/
def Path (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 : Array U32 8#usize) (post : PoolV1PairLiveSnapshotV1 → Prop) : Prop :=
  ∃ s17, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 544#usize, «end» := 576#usize }) = ok s17 ∧
  ∃ r39, (core.array.TryFromSharedArraySlice.try_from 32#usize s17) = ok r39 ∧
  ∃ a14, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r39) = ok a14 ∧
  ∃ r40, (atomic_statement.decode_digest_canonical a14) = ok r40 ∧
  ∃ r41, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r40 ()) = ok r41 ∧
  ∃ cf13, (core.result.Result.Insts.CoreOpsTry.branch r41) = ok cf13 ∧
  match cf13 with
  | core.ops.control_flow.ControlFlow.Continue val13 =>
    ∃ s18, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 576#usize, «end» := 608#usize }) = ok s18 ∧
    ∃ r42, (core.array.TryFromSharedArraySlice.try_from 32#usize s18) = ok r42 ∧
    ∃ a15, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r42) = ok a15 ∧
    ∃ r43, (atomic_statement.decode_digest_canonical a15) = ok r43 ∧
    ∃ r44, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r43 ()) = ok r44 ∧
    ∃ cf14, (core.result.Result.Insts.CoreOpsTry.branch r44) = ok cf14 ∧
    match cf14 with
    | core.ops.control_flow.ControlFlow.Continue val14 =>
      ∃ s19, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 608#usize, «end» := 640#usize }) = ok s19 ∧
      ∃ r45, (core.array.TryFromSharedArraySlice.try_from 32#usize s19) = ok r45 ∧
      ∃ a16, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r45) = ok a16 ∧
      ∃ r46, (atomic_statement.decode_digest_canonical a16) = ok r46 ∧
      ∃ r47, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r46 ()) = ok r47 ∧
      ∃ cf15, (core.result.Result.Insts.CoreOpsTry.branch r47) = ok cf15 ∧
      match cf15 with
      | core.ops.control_flow.ControlFlow.Continue val15 =>
        ∃ s20, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 640#usize, «end» := 672#usize }) = ok s20 ∧
        ∃ r48, (core.array.TryFromSharedArraySlice.try_from 32#usize s20) = ok r48 ∧
        ∃ a17, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r48) = ok a17 ∧
        ∃ r49, (atomic_statement.decode_digest_canonical a17) = ok r49 ∧
        ∃ r50, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r49 ()) = ok r50 ∧
        ∃ cf16, (core.result.Result.Insts.CoreOpsTry.branch r50) = ok cf16 ∧
        match cf16 with
        | core.ops.control_flow.ControlFlow.Continue val16 =>
          PV_RunJoin_CodecStage16Continuation30.Path bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 post
        | core.ops.control_flow.ControlFlow.Break residual => False
      | core.ops.control_flow.ControlFlow.Break residual => False
    | core.ops.control_flow.ControlFlow.Break residual => False
  | core.ops.control_flow.ControlFlow.Break residual => False

theorem path_wp (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 : Array U32 8#usize) (post : PoolV1PairLiveSnapshotV1 → Prop) :
    wp (PV_RunJoin_DecoderStage1229.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12) (accepts post) ↔ Path bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 post := by
  unfold PV_RunJoin_DecoderStage1229.run Path
  simp only [bind_wp,ite_wp,ok_wp,accepts,residual_accepts,PV_RunJoin_CodecStage16Continuation30.path_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,accepts,residual_accepts,PV_RunJoin_CodecStage16Continuation30.path_wp])
#print axioms path_wp
end R1Z.PV_RunJoin_CodecStage12Continuation30
