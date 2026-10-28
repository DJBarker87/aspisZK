import R1Z.PV_RunJoin_DecoderStage029
set_option autoImplicit false
namespace R1Z.PV_RunJoin_DecoderPrefix29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z.PV_RunJoin_DecoderStage2029

def run (bytes : Slice U8) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1) := do
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
                        let r ← core.array.TryFromSharedArraySlice.try_from 32#usize s4
                        let a1 ← atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r
                        let r1 ← atomic_statement.decode_digest_canonical a1
                        let r2 ← core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r1 ()
                        let cf ← core.result.Result.Insts.CoreOpsTry.branch r2
                        match cf with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          PV_RunJoin_DecoderStage029.run bytes val
                        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual

/-- Pure continuation factoring of the authoritative decoder, for all bytes.
No native body or primitive operation is replaced. -/
theorem source (bytes : Slice U8) : run bytes = decode_pool_v1_pair_live_snapshot_v1 bytes := by
  rfl
#print axioms source

theorem validated {bytes : Slice U8} {snapshot : PoolV1PairLiveSnapshotV1}
    (h : run bytes = ok (.Ok snapshot)) :
    validate_pool_v1_pair_live_snapshot_v1 snapshot = ok (.Ok ()) := by
  unfold run at h
  pv_head h
  repeat' first
    | exact PV_RunJoin_DecoderStage029.validated h
    | (have hr := branch_continue _ _ hvalue; clear hvalue; cases hr)
    | (pv_peel h with value hvalue; pv_head h)
    | (pv_if h <;> pv_head h)
    | exact False.elim (R1Z.PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (R1Z.PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> pv_head h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (cases h; assumption)
#print axioms validated
end R1Z.PV_RunJoin_DecoderPrefix29
