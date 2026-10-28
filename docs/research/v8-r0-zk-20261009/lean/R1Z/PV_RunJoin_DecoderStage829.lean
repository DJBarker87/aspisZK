import R1Z.PV_RunJoin_HeadControl29
import R1Z.PV_RunJoin_DecoderStage1229
import R1Z.PV_RunJoin_ResultDomain28
set_option autoImplicit false
namespace R1Z.PV_RunJoin_DecoderStage829
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open R1Z
open PV_RunJoin_DecoderStage2029

/-- Unchanged extracted continuation after canonical digest 8. -/
def run (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 : Array U32 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s13 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 416#usize, «end» := 448#usize }
  let r27 ← core.array.TryFromSharedArraySlice.try_from 32#usize s13
  let a10 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r27
  let r28 ← atomic_statement.decode_digest_canonical a10
  let r29 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r28 ()
  let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r29
  match cf9 with
  | core.ops.control_flow.ControlFlow.Continue val9 =>
    let s14 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 448#usize, «end» := 480#usize }
    let r30 ← core.array.TryFromSharedArraySlice.try_from 32#usize s14
    let a11 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r30
    let r31 ← atomic_statement.decode_digest_canonical a11
    let r32 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r31 ()
    let cf10 ← core.result.Result.Insts.CoreOpsTry.branch r32
    match cf10 with
    | core.ops.control_flow.ControlFlow.Continue val10 =>
      let s15 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 480#usize, «end» := 512#usize }
      let r33 ← core.array.TryFromSharedArraySlice.try_from 32#usize s15
      let a12 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r33
      let r34 ← atomic_statement.decode_digest_canonical a12
      let r35 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r34 ()
      let cf11 ← core.result.Result.Insts.CoreOpsTry.branch r35
      match cf11 with
      | core.ops.control_flow.ControlFlow.Continue val11 =>
        let s16 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 512#usize, «end» := 544#usize }
        let r36 ← core.array.TryFromSharedArraySlice.try_from 32#usize s16
        let a13 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r36
        let r37 ← atomic_statement.decode_digest_canonical a13
        let r38 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r37 ()
        let cf12 ← core.result.Result.Insts.CoreOpsTry.branch r38
        match cf12 with
        | core.ops.control_flow.ControlFlow.Continue val12 =>
          PV_RunJoin_DecoderStage1229.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

theorem validated {bytes : Slice U8} {val val1 val2 val3 val4 val5 val6 val7 val8 : Array U32 8#usize} {snapshot : PoolV1PairLiveSnapshotV1}
    (h : run bytes val val1 val2 val3 val4 val5 val6 val7 val8 = ok (.Ok snapshot)) :
    validate_pool_v1_pair_live_snapshot_v1 snapshot = ok (.Ok ()) := by
  unfold run at h
  pv_head h
  repeat' first
    | exact PV_RunJoin_DecoderStage1229.validated h
    | (have hr := branch_continue _ _ hvalue; clear hvalue; cases hr)
    | (pv_peel h with value hvalue; pv_head h)
    | (pv_if h <;> pv_head h)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> pv_head h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (cases h; assumption)
#print axioms validated
end R1Z.PV_RunJoin_DecoderStage829
