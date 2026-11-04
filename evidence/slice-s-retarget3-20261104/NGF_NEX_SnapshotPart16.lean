import Lean
import RPz7_S6NativeSnapshotDecoderFactoredV1

set_option autoImplicit false
noncomputable section
namespace NGF_NEX_SnapshotPart16
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
open pool_v1.pair_tree_profile AspisS6NativeSnapshotDecoderFactored
abbrev Read := Slice U8 → Result (core.result.Result (Array aspis_core.field.M31 8#usize) atomic_statement.AtomicStatementError)
abbrev Validate := PoolV1PairLiveSnapshotV1 → Result (core.result.Result Unit PoolV1PairLiveSnapshotErrorV1)
def run (read : Read) (validate : Validate) (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let s21 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 672#usize, «end» := 704#usize }
  let r52 ← read s21
  let r53 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r52 ()
  let cf17 ← core.result.Result.Insts.CoreOpsTry.branch r53
  match cf17 with
  | core.ops.control_flow.ControlFlow.Continue val17 =>
    let s22 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 704#usize, «end» := 736#usize }
    let r55 ← read s22
    let r56 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r55 ()
    let cf18 ← core.result.Result.Insts.CoreOpsTry.branch r56
    match cf18 with
    | core.ops.control_flow.ControlFlow.Continue val18 =>
      let s23 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 736#usize, «end» := 768#usize }
      let r58 ← read s23
      let r59 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r58 ()
      let cf19 ← core.result.Result.Insts.CoreOpsTry.branch r59
      match cf19 with
      | core.ops.control_flow.ControlFlow.Continue val19 =>
        let s24 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 768#usize, «end» := 800#usize }
        let r61 ← read s24
        let r62 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r61 ()
        let cf20 ← core.result.Result.Insts.CoreOpsTry.branch r62
        match cf20 with
        | core.ops.control_flow.ControlFlow.Continue val20 =>
          let s25 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }
          let a22 ← AspisS6NativeSnapshotReadArray.read_array 32#usize s25
          let s26 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }
          let a23 ← AspisS6NativeSnapshotReadArray.read_array 32#usize s26
          let s27 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 120#usize }
          let a24 ← AspisS6NativeSnapshotReadArray.read_array 8#usize s27
          let i9 ← lift (core.num.U64.from_le_bytes a24)
          let s28 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 120#usize, «end» := 128#usize }
          let a25 ← AspisS6NativeSnapshotReadArray.read_array 8#usize s28
          let i10 ← lift (core.num.U64.from_le_bytes a25)
          let r67 ← validate { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }
          let cf21 ← core.result.Result.Insts.CoreOpsTry.branch r67
          match cf21 with
          | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) })
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
theorem source (bytes : Slice U8) (val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 : Array aspis_core.field.M31 8#usize) :
    run AspisS6NativeSnapshotReadDigest.read_digest pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 = AspisS6NativeSnapshotDecoderFactored.part_16 bytes val val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 val11 val12 val13 val14 val15 val16 := by
  unfold run AspisS6NativeSnapshotDecoderFactored.part_16
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "NGF_NEX_Snapshot" || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl
#print axioms source
end NGF_NEX_SnapshotPart16

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
