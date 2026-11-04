import S6NativeSnapshotDecoderFactoredV1
import NEX_SnapshotPart4
set_option autoImplicit false
noncomputable section
namespace NEX_SnapshotPart0
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
open pool_v1.pair_tree_profile AspisS6NativeSnapshotDecoderFactored
abbrev Read := Slice U8 → Result (core.result.Result (Array aspis_core.field.M31 8#usize) atomic_statement.AtomicStatementError)
abbrev Validate := PoolV1PairLiveSnapshotV1 → Result (core.result.Result Unit PoolV1PairLiveSnapshotErrorV1)
def run (read : Read) (validate : Validate) (bytes : Slice U8) (val : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 160#usize, «end» := 192#usize }
  let r4 ← read s5
  let r5 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r4 ()
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let s6 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 192#usize, «end» := 224#usize }
    let r7 ← read s6
    let r8 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r7 ()
    let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r8
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      let s7 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 224#usize, «end» := 256#usize }
      let r10 ← read s7
      let r11 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r10 ()
      let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r11
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val3 =>
        let s8 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 256#usize, «end» := 288#usize }
        let r13 ← read s8
        let r14 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r13 ()
        let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r14
        match cf4 with
        | core.ops.control_flow.ControlFlow.Continue val4 =>
          NEX_SnapshotPart4.run read validate bytes val val1 val2 val3 val4
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
theorem source (bytes : Slice U8) (val : Array aspis_core.field.M31 8#usize) :
    run AspisS6NativeSnapshotReadDigest.read_digest pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 bytes val = AspisS6NativeSnapshotDecoderFactored.part_0 bytes val := by
  unfold run AspisS6NativeSnapshotDecoderFactored.part_0
  simp only [NEX_SnapshotPart4.source]
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
end NEX_SnapshotPart0
