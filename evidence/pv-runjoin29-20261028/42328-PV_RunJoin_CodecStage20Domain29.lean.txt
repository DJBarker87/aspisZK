import R1Z.PV_RunJoin_DecoderStage2029
import R1Z.PV_RunJoin_RejectionProof28
import R1Z.PV_RunJoin_BranchDomain28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CodecStage20Domain29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28

/-- Source primitives and branch guards only; no whole-decoder success premise. -/
def Path (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 : Array U32 8#usize) : Prop :=
  ∃ s25, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }) = ok s25 ∧
  ∃ r63, (core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s25) = ok r63 ∧
  ∃ a22, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r63) = ok a22 ∧
  ∃ s26, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }) = ok s26 ∧
  ∃ r64, (core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s26) = ok r64 ∧
  ∃ a23, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r64) = ok a23 ∧
  ∃ s27, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 120#usize }) = ok s27 ∧
  ∃ r65, (core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s27) = ok r65 ∧
  ∃ a24, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r65) = ok a24 ∧
  ∃ i9, (lift (core.num.U64.from_le_bytes a24)) = ok i9 ∧
  ∃ s28, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 120#usize, «end» := 128#usize }) = ok s28 ∧
  ∃ r66, (core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s28) = ok r66 ∧
  ∃ a25, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r66) = ok a25 ∧
  ∃ i10, (lift (core.num.U64.from_le_bytes a25)) = ok i10 ∧
  ∃ r67, (pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }) = ok r67 ∧
  ∃ cf21, (core.result.Result.Insts.CoreOpsTry.branch r67) = ok cf21 ∧
  match cf21 with
  | core.ops.control_flow.ControlFlow.Continue _ => True
  | core.ops.control_flow.ControlFlow.Break residual => False

/-- Every first-error path retains its entire successful prefix. -/
def ErrorPath (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 : Array U32 8#usize) (error : PoolV1PairLiveSnapshotErrorV1) : Prop :=
  ∃ s25, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }) = ok s25 ∧
  ∃ r63, (core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s25) = ok r63 ∧
  ∃ a22, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r63) = ok a22 ∧
  ∃ s26, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }) = ok s26 ∧
  ∃ r64, (core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s26) = ok r64 ∧
  ∃ a23, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r64) = ok a23 ∧
  ∃ s27, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 120#usize }) = ok s27 ∧
  ∃ r65, (core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s27) = ok r65 ∧
  ∃ a24, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r65) = ok a24 ∧
  ∃ i9, (lift (core.num.U64.from_le_bytes a24)) = ok i9 ∧
  ∃ s28, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 120#usize, «end» := 128#usize }) = ok s28 ∧
  ∃ r66, (core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s28) = ok r66 ∧
  ∃ a25, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r66) = ok a25 ∧
  ∃ i10, (lift (core.num.U64.from_le_bytes a25)) = ok i10 ∧
  ∃ r67, (pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }) = ok r67 ∧
  ∃ cf21, (core.result.Result.Insts.CoreOpsTry.branch r67) = ok cf21 ∧
  match cf21 with
  | core.ops.control_flow.ControlFlow.Continue _ => False
  | core.ops.control_flow.ControlFlow.Break residual => (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual) = ok (.Err error)

theorem success_iff (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 : Array U32 8#usize) : (∃ snapshot, PV_RunJoin_DecoderStage2029.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 = ok (.Ok snapshot)) ↔ Path bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 := by
  rw [R1Z.PV_RunJoin_ResultDomain28.success_wp]
  unfold PV_RunJoin_DecoderStage2029.run Path
  simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp])
#print axioms success_iff

theorem error_iff (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 : Array U32 8#usize) (error : PoolV1PairLiveSnapshotErrorV1) : PV_RunJoin_DecoderStage2029.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 = ok (.Err error) ↔ ErrorPath bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 error := by
  rw [eq_wp]
  unfold PV_RunJoin_DecoderStage2029.run ErrorPath
  simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq])
#print axioms error_iff

theorem path_wp (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 : Array U32 8#usize) : wp (PV_RunJoin_DecoderStage2029.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20) isRustOk ↔ Path bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 :=
  (R1Z.PV_RunJoin_ResultDomain28.success_wp _).symm.trans (success_iff bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20)
#print axioms path_wp

theorem error_wp (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 : Array U32 8#usize) (error : PoolV1PairLiveSnapshotErrorV1) :
    wp (PV_RunJoin_DecoderStage2029.run bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20) (fun x => x = .Err error) ↔ ErrorPath bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 error :=
  (eq_wp _ _).symm.trans (error_iff bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 val17 val18 val19 val20 error)
#print axioms error_wp
end R1Z.PV_RunJoin_CodecStage20Domain29
