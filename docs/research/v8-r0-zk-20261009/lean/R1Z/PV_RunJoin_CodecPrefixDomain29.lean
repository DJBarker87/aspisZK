import R1Z.PV_RunJoin_DecoderPrefix29
import R1Z.PV_RunJoin_RejectionProof28
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_CodecStage0Domain29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CodecPrefixDomain29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_tree_profile R1Z
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28

/-- Source primitives and branch guards only; no whole-decoder success premise. -/
def Path (bytes : Slice U8) : Prop :=
  let i := Slice.len bytes
  if i != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  then False
  else
    ∃ s, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 8#usize }) = ok s ∧
    ∃ s1, (core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC { start := 0#usize, «end» := 8#usize }) = ok s1 ∧
    ∃ b, (core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1) = ok b ∧
    if b
    then False
    else
      ∃ i1, (Slice.index_usize bytes 8#usize) = ok i1 ∧
      if i1 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
      then False
      else
        ∃ i2, (Slice.index_usize bytes 9#usize) = ok i2 ∧
        if i2 != 0#u8
        then False
        else
          ∃ i3, (Slice.index_usize bytes 10#usize) = ok i3 ∧
          if i3 != 0#u8
          then False
          else
            ∃ i4, (Slice.index_usize bytes 11#usize) = ok i4 ∧
            if i4 != 0#u8
            then False
            else
              ∃ i5, (Slice.index_usize bytes 12#usize) = ok i5 ∧
              if i5 != 0#u8
              then False
              else
                ∃ i6, (Slice.index_usize bytes 13#usize) = ok i6 ∧
                if i6 != 0#u8
                then False
                else
                  ∃ i7, (Slice.index_usize bytes 14#usize) = ok i7 ∧
                  if i7 != 0#u8
                  then False
                  else
                    ∃ i8, (Slice.index_usize bytes 15#usize) = ok i8 ∧
                    if i8 != 0#u8
                    then False
                    else
                      ∃ s2, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize }) = ok s2 ∧
                      ∃ a, (pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING) = ok a ∧
                      ∃ s3, (core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a { start := 0#usize, «end» := 32#usize }) = ok s3 ∧
                      ∃ b1, (core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s2 s3) = ok b1 ∧
                      if b1
                      then False
                      else
                        ∃ s4, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 128#usize, «end» := 160#usize }) = ok s4 ∧
                        ∃ r, (core.array.TryFromSharedArraySlice.try_from 32#usize s4) = ok r ∧
                        ∃ a1, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r) = ok a1 ∧
                        ∃ r1, (atomic_statement.decode_digest_canonical a1) = ok r1 ∧
                        ∃ r2, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r1 ()) = ok r2 ∧
                        ∃ cf, (core.result.Result.Insts.CoreOpsTry.branch r2) = ok cf ∧
                        match cf with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          PV_RunJoin_CodecStage0Domain29.Path bytes val
                        | core.ops.control_flow.ControlFlow.Break residual => False

/-- Every first-error path retains its entire successful prefix. -/
def ErrorPath (bytes : Slice U8) (error : PoolV1PairLiveSnapshotErrorV1) : Prop :=
  let i := Slice.len bytes
  if i != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
  else
    ∃ s, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 8#usize }) = ok s ∧
    ∃ s1, (core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC { start := 0#usize, «end» := 8#usize }) = ok s1 ∧
    ∃ b, (core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1) = ok b ∧
    if b
    then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongMagic) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
    else
      ∃ i1, (Slice.index_usize bytes 8#usize) = ok i1 ∧
      if i1 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
      then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongVersion) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
      else
        ∃ i2, (Slice.index_usize bytes 9#usize) = ok i2 ∧
        if i2 != 0#u8
        then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
        else
          ∃ i3, (Slice.index_usize bytes 10#usize) = ok i3 ∧
          if i3 != 0#u8
          then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
          else
            ∃ i4, (Slice.index_usize bytes 11#usize) = ok i4 ∧
            if i4 != 0#u8
            then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
            else
              ∃ i5, (Slice.index_usize bytes 12#usize) = ok i5 ∧
              if i5 != 0#u8
              then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
              else
                ∃ i6, (Slice.index_usize bytes 13#usize) = ok i6 ∧
                if i6 != 0#u8
                then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
                else
                  ∃ i7, (Slice.index_usize bytes 14#usize) = ok i7 ∧
                  if i7 != 0#u8
                  then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
                  else
                    ∃ i8, (Slice.index_usize bytes 15#usize) = ok i8 ∧
                    if i8 != 0#u8
                    then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
                    else
                      ∃ s2, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize }) = ok s2 ∧
                      ∃ a, (pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING) = ok a ∧
                      ∃ s3, (core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a { start := 0#usize, «end» := 32#usize }) = ok s3 ∧
                      ∃ b1, (core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s2 s3) = ok b1 ∧
                      if b1
                      then (ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongFormatBinding) : Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)) = ok (.Err error)
                      else
                        ∃ s4, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 128#usize, «end» := 160#usize }) = ok s4 ∧
                        ∃ r, (core.array.TryFromSharedArraySlice.try_from 32#usize s4) = ok r ∧
                        ∃ a1, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r) = ok a1 ∧
                        ∃ r1, (atomic_statement.decode_digest_canonical a1) = ok r1 ∧
                        ∃ r2, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r1 ()) = ok r2 ∧
                        ∃ cf, (core.result.Result.Insts.CoreOpsTry.branch r2) = ok cf ∧
                        match cf with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          PV_RunJoin_CodecStage0Domain29.ErrorPath bytes val error
                        | core.ops.control_flow.ControlFlow.Break residual => (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual) = ok (.Err error)

theorem success_iff (bytes : Slice U8) : (∃ snapshot, PV_RunJoin_DecoderPrefix29.run bytes = ok (.Ok snapshot)) ↔ Path bytes := by
  rw [R1Z.PV_RunJoin_ResultDomain28.success_wp]
  unfold PV_RunJoin_DecoderPrefix29.run Path
  simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp,PV_RunJoin_CodecStage0Domain29.path_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp,PV_RunJoin_CodecStage0Domain29.path_wp])
#print axioms success_iff

theorem error_iff (bytes : Slice U8) (error : PoolV1PairLiveSnapshotErrorV1) : PV_RunJoin_DecoderPrefix29.run bytes = ok (.Err error) ↔ ErrorPath bytes error := by
  rw [eq_wp]
  unfold PV_RunJoin_DecoderPrefix29.run ErrorPath
  simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq,PV_RunJoin_CodecStage0Domain29.error_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq,PV_RunJoin_CodecStage0Domain29.error_wp])
#print axioms error_iff
end R1Z.PV_RunJoin_CodecPrefixDomain29
