import S6NativeSnapshotDecoderFactoredV1
import NEX_SnapshotPart0
set_option autoImplicit false
noncomputable section
namespace NEX_SnapshotParent
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
open pool_v1.pair_tree_profile AspisS6NativeSnapshotDecoderFactored
abbrev Read := Slice U8 → Result (core.result.Result (Array aspis_core.field.M31 8#usize) atomic_statement.AtomicStatementError)
abbrev Validate := PoolV1PairLiveSnapshotV1 → Result (core.result.Result Unit PoolV1PairLiveSnapshotErrorV1)
def run (read : Read) (validate : Validate) (bytes : Slice U8) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
  let i := Slice.len bytes
  if i != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength)
  else
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 8#usize }
    let s1 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC { start := 0#usize, «end» := 8#usize }
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1
    if b
    then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongMagic)
    else
      let i1 ← Slice.index_usize bytes 8#usize
      if i1 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
      then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongVersion)
      else
        let i2 ← Slice.index_usize bytes 9#usize
        if i2 != 0#u8
        then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
        else
          let i3 ← Slice.index_usize bytes 10#usize
          if i3 != 0#u8
          then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
          else
            let i4 ← Slice.index_usize bytes 11#usize
            if i4 != 0#u8
            then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
            else
              let i5 ← Slice.index_usize bytes 12#usize
              if i5 != 0#u8
              then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
              else
                let i6 ← Slice.index_usize bytes 13#usize
                if i6 != 0#u8
                then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                else
                  let i7 ← Slice.index_usize bytes 14#usize
                  if i7 != 0#u8
                  then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                  else
                    let i8 ← Slice.index_usize bytes 15#usize
                    if i8 != 0#u8
                    then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                    else
                      let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize }
                      let a ← pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
                      let s3 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a { start := 0#usize, «end» := 32#usize }
                      let b1 ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s2 s3
                      if b1
                      then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongFormatBinding)
                      else
                        let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 128#usize, «end» := 160#usize }
                        let r1 ← read s4
                        let r2 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r1 ()
                        let cf ← core.result.Result.Insts.CoreOpsTry.branch r2
                        match cf with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          NEX_SnapshotPart0.run read validate bytes val
                        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual
theorem source (bytes : Slice U8) :
    run AspisS6NativeSnapshotReadDigest.read_digest pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 bytes = AspisS6NativeSnapshotDecoderFactored.decode bytes := by
  unfold run AspisS6NativeSnapshotDecoderFactored.decode
  simp only [NEX_SnapshotPart0.source]
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

/-- Substitute both certified child models into the explicit full-Result G.
The existing factored/source equality supplies the original cohort endpoint. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (run AspisS6NativeSnapshotReadDigest.read_digest pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 bytes,state,([] : List Unit)) =
    (decode_pool_v1_pair_live_snapshot_v1 bytes,state,[]) := by
  exact congrArg (fun r => (r,state,([] : List Unit)))
    ((source bytes).trans (AspisS6NativeSnapshotDecoderFactored.decode_source bytes))
#print axioms result_state_effects
end NEX_SnapshotParent
