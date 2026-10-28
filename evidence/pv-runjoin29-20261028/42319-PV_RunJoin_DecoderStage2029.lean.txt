import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_HeadControl29
import R1Z.PV_RunJoin_ResultDomain28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DecoderStage2029
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open R1Z


/-- Unchanged extracted continuation after canonical digest 20. -/
def run (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 : Array U32 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s25 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }
  let r63 ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s25
  let a22 ← atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r63
  let s26 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }
  let r64 ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s26
  let a23 ← atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r64
  let s27 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 120#usize }
  let r65 ← core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s27
  let a24 ← atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r65
  let i9 ← lift (core.num.U64.from_le_bytes a24)
  let s28 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 120#usize, «end» := 128#usize }
  let r66 ← core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s28
  let a25 ← atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r66
  let i10 ← lift (core.num.U64.from_le_bytes a25)
  let r67 ← pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }
  let cf21 ← core.result.Result.Insts.CoreOpsTry.branch r67
  match cf21 with
  | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) })
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

theorem branch_continue {α ε : Type} (r : core.result.Result α ε) (a : α)
    (h : core.result.Result.Insts.CoreOpsTry.branch r = ok (.Continue a)) : r = .Ok a := by
  cases r with
  | Ok b => cases h; rfl
  | Err e => cases h
#print axioms branch_continue

theorem validated {bytes : Slice U8} {val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 : Array U32 8#usize} {snapshot : PoolV1PairLiveSnapshotV1}
    (h : run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 = ok (.Ok snapshot)) :
    validate_pool_v1_pair_live_snapshot_v1 snapshot = ok (.Ok ()) := by
  unfold run at h
  pv_head h
  repeat' first
    | (have hr := branch_continue _ _ hvalue; clear hvalue; cases hr)
    | (pv_peel h with value hvalue; pv_head h)
    | (pv_if h <;> pv_head h)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> pv_head h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (cases h; assumption)
#print axioms validated
end R1Z.PV_RunJoin_DecoderStage2029
