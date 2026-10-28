import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_HeadControl29
import R1Z.PV_RunJoin_DecoderStage2029
import R1Z.PV_RunJoin_ResultDomain28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DecoderStage1629
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open R1Z
open PV_RunJoin_DecoderStage2029

/-- Unchanged extracted continuation after canonical digest 16. -/
def run (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array U32 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s21 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 672#usize, «end» := 704#usize }
  let r51 ← core.array.TryFromSharedArraySlice.try_from 32#usize s21
  let a18 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r51
  let r52 ← atomic_statement.decode_digest_canonical a18
  let r53 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r52 ()
  let cf17 ← core.result.Result.Insts.CoreOpsTry.branch r53
  match cf17 with
  | core.ops.control_flow.ControlFlow.Continue val17 =>
    let s22 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 704#usize, «end» := 736#usize }
    let r54 ← core.array.TryFromSharedArraySlice.try_from 32#usize s22
    let a19 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r54
    let r55 ← atomic_statement.decode_digest_canonical a19
    let r56 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r55 ()
    let cf18 ← core.result.Result.Insts.CoreOpsTry.branch r56
    match cf18 with
    | core.ops.control_flow.ControlFlow.Continue val18 =>
      let s23 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 736#usize, «end» := 768#usize }
      let r57 ← core.array.TryFromSharedArraySlice.try_from 32#usize s23
      let a20 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r57
      let r58 ← atomic_statement.decode_digest_canonical a20
      let r59 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r58 ()
      let cf19 ← core.result.Result.Insts.CoreOpsTry.branch r59
      match cf19 with
      | core.ops.control_flow.ControlFlow.Continue val19 =>
        let s24 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 768#usize, «end» := 800#usize }
        let r60 ← core.array.TryFromSharedArraySlice.try_from 32#usize s24
        let a21 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r60
        let r61 ← atomic_statement.decode_digest_canonical a21
        let r62 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r61 ()
        let cf20 ← core.result.Result.Insts.CoreOpsTry.branch r62
        match cf20 with
        | core.ops.control_flow.ControlFlow.Continue val20 =>
          PV_RunJoin_DecoderStage2029.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

theorem validated {bytes : Slice U8} {val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array U32 8#usize} {snapshot : PoolV1PairLiveSnapshotV1}
    (h : run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 = ok (.Ok snapshot)) :
    validate_pool_v1_pair_live_snapshot_v1 snapshot = ok (.Ok ()) := by
  unfold run at h
  pv_head h
  repeat' first
    | exact PV_RunJoin_DecoderStage2029.validated h
    | (have hr := branch_continue _ _ hvalue; clear hvalue; cases hr)
    | (pv_peel h with value hvalue; pv_head h)
    | (pv_if h <;> pv_head h)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> pv_head h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (cases h; assumption)
#print axioms validated
end R1Z.PV_RunJoin_DecoderStage1629
