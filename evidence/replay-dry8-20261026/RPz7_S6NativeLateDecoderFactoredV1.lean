import RPz7_S6NativeLateChildDecodeV1
import RPz7_S6NativeSnapshotReadArrayV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisS6NativeLateDecoderFactored
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def decode (bytes : Slice Std.U8) : Result (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) := do
  let i := Slice.len bytes
  let i1 ← pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
  if i != i1
  then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongLength)
  else
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 8#usize }
    let s1 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC { start := 0#usize, «end» := 8#usize }
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1
    if b
    then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongMagic)
    else
      let i2 ← Slice.index_usize bytes 8#usize
      if i2 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
      then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongVersion)
      else
        let i3 ← Slice.index_usize bytes 9#usize
        if i3 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
        then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongItemCount)
        else
          let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 10#usize, «end» := 12#usize }
          let a ← AspisS6NativeSnapshotReadArray.read_array 2#usize s2
          let i4 ← lift (core.num.U16.from_le_bytes a)
          let i5 ← lift (UScalar.cast .Usize i4)
          if i5 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
          then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongHeaderLength)
          else
            let s3 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 12#usize, «end» := 16#usize }
            let a1 ← AspisS6NativeSnapshotReadArray.read_array 4#usize s3
            let i6 ← lift (core.num.U32.from_le_bytes a1)
            let i7 ← lift (UScalar.cast .Usize i6)
            if i7 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
            then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongSnapshotLength)
            else
              let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 20#usize }
              let a2 ← AspisS6NativeSnapshotReadArray.read_array 4#usize s4
              let i8 ← lift (core.num.U32.from_le_bytes a2)
              let i9 ← lift (UScalar.cast .Usize i8)
              let i10 ← pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
              if i9 != i10
              then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongAfterstateLength)
              else
                let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 20#usize, «end» := 24#usize }
                let a3 ← AspisS6NativeSnapshotReadArray.read_array 4#usize s5
                let i11 ← lift (core.num.U32.from_le_bytes a3)
                let i12 ← lift (UScalar.cast .Usize i11)
                if i12 != i1
                then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongTotalLength)
                else
                  let i13 ← Slice.index_usize bytes 24#usize
                  if i13 != 0#u8
                  then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                  else
                    let i14 ← Slice.index_usize bytes 25#usize
                    if i14 != 0#u8
                    then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                    else
                      let i15 ← Slice.index_usize bytes 26#usize
                      if i15 != 0#u8
                      then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                      else
                        let i16 ← Slice.index_usize bytes 27#usize
                        if i16 != 0#u8
                        then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                        else
                          let i17 ← Slice.index_usize bytes 28#usize
                          if i17 != 0#u8
                          then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                          else
                            let i18 ← Slice.index_usize bytes 29#usize
                            if i18 != 0#u8
                            then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                            else
                              let i19 ← Slice.index_usize bytes 30#usize
                              if i19 != 0#u8
                              then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                              else
                                let i20 ← Slice.index_usize bytes 31#usize
                                if i20 != 0#u8
                                then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved)
                                else
                                  let i21 ← 32#usize + pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
                                  let s6 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 32#usize, «end» := i21 }
                                  let r4 ← pool_v1.pair_tree_profile.decode_pair_live_snapshot_boxed_v1 s6
                                  let cf ← core.result.Result.Insts.CoreOpsTry.branch r4
                                  match cf with
                                  | core.ops.control_flow.ControlFlow.Continue val =>
                                    let s7 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes { start := i21 }
                                    let r5 ← pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1 s7
                                    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
                                    match cf1 with
                                    | core.ops.control_flow.ControlFlow.Continue val1 => let o ← lift (U64.checked_add val.next_pair_index 1#u64)
                                                                                         let b1 ← core.cmp.PartialEq.ne.trait_default (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64) o (some val1.next_pair_index)
                                                                                         if b1
                                                                                         then ok (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.AfterstateIndexMismatch)
                                                                                         else ok (core.result.Result.Ok { live_snapshot := val, candidate_afterstate := val1 })
                                    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual
                                  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual



theorem decode_source (bytes : Slice U8) :
    decode bytes=decode_pool_v1_pair_late_public_statement_boxed_v1 bytes := by
  unfold decode decode_pool_v1_pair_late_public_statement_boxed_v1
  unfold AspisS6NativeSnapshotReadArray.read_array
  simp only [bind_assoc_eq]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeLateDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

#print axioms decode_source
end AspisS6NativeLateDecoderFactored
