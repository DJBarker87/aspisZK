import R1Z.PV_RunJoin_DecoderStage029
import R1Z.PV_RunJoin_RejectionProof28
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_CodecStage4Domain29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CodecStage0Domain29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28

/-- Source primitives and branch guards only; no whole-decoder success premise. -/
def Path (bytes : Slice U8) (val : Array U32 8#usize) : Prop :=
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
          PV_RunJoin_CodecStage4Domain29.Path bytes val val1 val2 val3 val4
        | core.ops.control_flow.ControlFlow.Break residual => False
      | core.ops.control_flow.ControlFlow.Break residual => False
    | core.ops.control_flow.ControlFlow.Break residual => False
  | core.ops.control_flow.ControlFlow.Break residual => False

/-- Every first-error path retains its entire successful prefix. -/
def ErrorPath (bytes : Slice U8) (val : Array U32 8#usize) (error : PoolV1PairLiveSnapshotErrorV1) : Prop :=
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
          PV_RunJoin_CodecStage4Domain29.ErrorPath bytes val val1 val2 val3 val4 error
        | core.ops.control_flow.ControlFlow.Break residual => (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual) = ok (.Err error)
      | core.ops.control_flow.ControlFlow.Break residual => (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual) = ok (.Err error)
    | core.ops.control_flow.ControlFlow.Break residual => (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual) = ok (.Err error)
  | core.ops.control_flow.ControlFlow.Break residual => (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual) = ok (.Err error)

theorem success_iff (bytes : Slice U8) (val : Array U32 8#usize) : (∃ snapshot, PV_RunJoin_DecoderStage029.run bytes val = ok (.Ok snapshot)) ↔ Path bytes val := by
  rw [R1Z.PV_RunJoin_ResultDomain28.success_wp]
  unfold PV_RunJoin_DecoderStage029.run Path
  simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp,PV_RunJoin_CodecStage4Domain29.path_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp,PV_RunJoin_CodecStage4Domain29.path_wp])
#print axioms success_iff

theorem error_iff (bytes : Slice U8) (val : Array U32 8#usize) (error : PoolV1PairLiveSnapshotErrorV1) : PV_RunJoin_DecoderStage029.run bytes val = ok (.Err error) ↔ ErrorPath bytes val error := by
  rw [eq_wp]
  unfold PV_RunJoin_DecoderStage029.run ErrorPath
  simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq,PV_RunJoin_CodecStage4Domain29.error_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq,PV_RunJoin_CodecStage4Domain29.error_wp])
#print axioms error_iff

theorem path_wp (bytes : Slice U8) (val : Array U32 8#usize) : wp (PV_RunJoin_DecoderStage029.run bytes val) isRustOk ↔ Path bytes val :=
  (R1Z.PV_RunJoin_ResultDomain28.success_wp _).symm.trans (success_iff bytes val)
#print axioms path_wp

theorem error_wp (bytes : Slice U8) (val : Array U32 8#usize) (error : PoolV1PairLiveSnapshotErrorV1) :
    wp (PV_RunJoin_DecoderStage029.run bytes val) (fun x => x = .Err error) ↔ ErrorPath bytes val error :=
  (eq_wp _ _).symm.trans (error_iff bytes val error)
#print axioms error_wp
end R1Z.PV_RunJoin_CodecStage0Domain29
