import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_HeadControl29
import R1Z.PV_RunJoin_DecoderStage429
import R1Z.PV_RunJoin_ResultDomain28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DecoderStage029
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open R1Z
open PV_RunJoin_DecoderStage2029

/-- Unchanged extracted continuation after canonical digest 0. -/
def run (bytes : Slice U8) (val : Array U32 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 160#usize, «end» := 192#usize }
  let r3 ← core.array.TryFromSharedArraySlice.try_from 32#usize s5
  let a2 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r3
  let r4 ← atomic_statement.decode_digest_canonical a2
  let r5 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r4 ()
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let s6 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 192#usize, «end» := 224#usize }
    let r6 ← core.array.TryFromSharedArraySlice.try_from 32#usize s6
    let a3 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r6
    let r7 ← atomic_statement.decode_digest_canonical a3
    let r8 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r7 ()
    let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r8
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      let s7 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 224#usize, «end» := 256#usize }
      let r9 ← core.array.TryFromSharedArraySlice.try_from 32#usize s7
      let a4 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r9
      let r10 ← atomic_statement.decode_digest_canonical a4
      let r11 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r10 ()
      let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r11
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val3 =>
        let s8 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 256#usize, «end» := 288#usize }
        let r12 ← core.array.TryFromSharedArraySlice.try_from 32#usize s8
        let a5 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r12
        let r13 ← atomic_statement.decode_digest_canonical a5
        let r14 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r13 ()
        let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r14
        match cf4 with
        | core.ops.control_flow.ControlFlow.Continue val4 =>
          PV_RunJoin_DecoderStage429.run bytes val val1 val2 val3 val4
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

theorem validated {bytes : Slice U8} {val : Array U32 8#usize} {snapshot : PoolV1PairLiveSnapshotV1}
    (h : run bytes val = ok (.Ok snapshot)) :
    validate_pool_v1_pair_live_snapshot_v1 snapshot = ok (.Ok ()) := by
  unfold run at h
  pv_head h
  repeat' first
    | exact PV_RunJoin_DecoderStage429.validated h
    | (have hr := branch_continue _ _ hvalue; clear hvalue; cases hr)
    | (pv_peel h with value hvalue; pv_head h)
    | (pv_if h <;> pv_head h)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> pv_head h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (cases h; assumption)
#print axioms validated
end R1Z.PV_RunJoin_DecoderStage029
