import R1Z.PV_RunJoin_HeadControl29
import R1Z.PV_RunJoin_DecoderStage829
import R1Z.PV_RunJoin_ResultDomain28
set_option autoImplicit false
namespace R1Z.PV_RunJoin_DecoderStage429
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open R1Z
open PV_RunJoin_DecoderStage2029

/-- Unchanged extracted continuation after canonical digest 4. -/
def run (bytes : Slice U8) (val val1 val2 val3 val4 : Array U32 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s9 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 288#usize, «end» := 320#usize }
  let r15 ← core.array.TryFromSharedArraySlice.try_from 32#usize s9
  let a6 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r15
  let r16 ← atomic_statement.decode_digest_canonical a6
  let r17 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r16 ()
  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r17
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue val5 =>
    let s10 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 320#usize, «end» := 352#usize }
    let r18 ← core.array.TryFromSharedArraySlice.try_from 32#usize s10
    let a7 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r18
    let r19 ← atomic_statement.decode_digest_canonical a7
    let r20 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r19 ()
    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r20
    match cf6 with
    | core.ops.control_flow.ControlFlow.Continue val6 =>
      let s11 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 352#usize, «end» := 384#usize }
      let r21 ← core.array.TryFromSharedArraySlice.try_from 32#usize s11
      let a8 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r21
      let r22 ← atomic_statement.decode_digest_canonical a8
      let r23 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r22 ()
      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r23
      match cf7 with
      | core.ops.control_flow.ControlFlow.Continue val7 =>
        let s12 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 384#usize, «end» := 416#usize }
        let r24 ← core.array.TryFromSharedArraySlice.try_from 32#usize s12
        let a9 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r24
        let r25 ← atomic_statement.decode_digest_canonical a9
        let r26 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r25 ()
        let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r26
        match cf8 with
        | core.ops.control_flow.ControlFlow.Continue val8 =>
          PV_RunJoin_DecoderStage829.run bytes val val1 val2 val3 val4 val5 val6 val7 val8
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

theorem validated {bytes : Slice U8} {val val1 val2 val3 val4 : Array U32 8#usize} {snapshot : PoolV1PairLiveSnapshotV1}
    (h : run bytes val val1 val2 val3 val4 = ok (.Ok snapshot)) :
    validate_pool_v1_pair_live_snapshot_v1 snapshot = ok (.Ok ()) := by
  unfold run at h
  pv_head h
  repeat' first
    | exact PV_RunJoin_DecoderStage829.validated h
    | (have hr := branch_continue _ _ hvalue; clear hvalue; cases hr)
    | (pv_peel h with value hvalue; pv_head h)
    | (pv_if h <;> pv_head h)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> pv_head h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (cases h; assumption)
#print axioms validated
end R1Z.PV_RunJoin_DecoderStage429
