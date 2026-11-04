import S6NativeSnapshotDecoderFactoredV1
import NEX_SnapshotPart12
set_option autoImplicit false
noncomputable section
namespace NEX_SnapshotPart8
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
open pool_v1.pair_tree_profile AspisS6NativeSnapshotDecoderFactored
abbrev Read := Slice U8 → Result (core.result.Result (Array aspis_core.field.M31 8#usize) atomic_statement.AtomicStatementError)
abbrev Validate := PoolV1PairLiveSnapshotV1 → Result (core.result.Result Unit PoolV1PairLiveSnapshotErrorV1)
def run (read : Read) (validate : Validate) (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s13 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 416#usize, «end» := 448#usize }
  let r28 ← read s13
  let r29 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r28 ()
  let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r29
  match cf9 with
  | core.ops.control_flow.ControlFlow.Continue val9 =>
    let s14 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 448#usize, «end» := 480#usize }
    let r31 ← read s14
    let r32 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r31 ()
    let cf10 ← core.result.Result.Insts.CoreOpsTry.branch r32
    match cf10 with
    | core.ops.control_flow.ControlFlow.Continue val10 =>
      let s15 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 480#usize, «end» := 512#usize }
      let r34 ← read s15
      let r35 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r34 ()
      let cf11 ← core.result.Result.Insts.CoreOpsTry.branch r35
      match cf11 with
      | core.ops.control_flow.ControlFlow.Continue val11 =>
        let s16 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 512#usize, «end» := 544#usize }
        let r37 ← read s16
        let r38 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r37 ()
        let cf12 ← core.result.Result.Insts.CoreOpsTry.branch r38
        match cf12 with
        | core.ops.control_flow.ControlFlow.Continue val12 =>
          NEX_SnapshotPart12.run read validate bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
theorem source (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 : Array aspis_core.field.M31 8#usize) :
    run AspisS6NativeSnapshotReadDigest.read_digest pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 bytes val val1 val2 val3 val4 val5 val6 val7 val8 = AspisS6NativeSnapshotDecoderFactored.part_8 bytes val val1 val2 val3 val4 val5 val6 val7 val8 := by
  unfold run AspisS6NativeSnapshotDecoderFactored.part_8
  simp only [NEX_SnapshotPart12.source]
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
end NEX_SnapshotPart8
