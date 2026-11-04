import S6NativeSnapshotDecoderFactoredV1
import NEX_SnapshotPart8
set_option autoImplicit false
noncomputable section
namespace NEX_SnapshotPart4
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
open pool_v1.pair_tree_profile AspisS6NativeSnapshotDecoderFactored
abbrev Read := Slice U8 → Result (core.result.Result (Array aspis_core.field.M31 8#usize) atomic_statement.AtomicStatementError)
abbrev Validate := PoolV1PairLiveSnapshotV1 → Result (core.result.Result Unit PoolV1PairLiveSnapshotErrorV1)
def run (read : Read) (validate : Validate) (bytes : Slice U8) (val val1 val2 val3 val4 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s9 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 288#usize, «end» := 320#usize }
  let r16 ← read s9
  let r17 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r16 ()
  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r17
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue val5 =>
    let s10 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 320#usize, «end» := 352#usize }
    let r19 ← read s10
    let r20 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r19 ()
    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r20
    match cf6 with
    | core.ops.control_flow.ControlFlow.Continue val6 =>
      let s11 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 352#usize, «end» := 384#usize }
      let r22 ← read s11
      let r23 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r22 ()
      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r23
      match cf7 with
      | core.ops.control_flow.ControlFlow.Continue val7 =>
        let s12 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 384#usize, «end» := 416#usize }
        let r25 ← read s12
        let r26 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r25 ()
        let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r26
        match cf8 with
        | core.ops.control_flow.ControlFlow.Continue val8 =>
          NEX_SnapshotPart8.run read validate bytes val val1 val2 val3 val4 val5 val6 val7 val8
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
theorem source (bytes : Slice U8) (val val1 val2 val3 val4 : Array aspis_core.field.M31 8#usize) :
    run AspisS6NativeSnapshotReadDigest.read_digest pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 bytes val val1 val2 val3 val4 = AspisS6NativeSnapshotDecoderFactored.part_4 bytes val val1 val2 val3 val4 := by
  unfold run AspisS6NativeSnapshotDecoderFactored.part_4
  simp only [NEX_SnapshotPart8.source]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "NEX_Snapshot" || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl
#print axioms source
end NEX_SnapshotPart4
