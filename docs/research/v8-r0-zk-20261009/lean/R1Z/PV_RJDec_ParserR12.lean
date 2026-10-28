import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser03
import R1Z.PV_RJDec_Parser14
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_ParserR12
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Slice Std.U8) :
  P (core.result.Result pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) := do
  let i := Slice.len bytes
  if i != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES then
    pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength)
  else
    let s ← invoke "core.slice.index.Slice.index" (fun ops =>
        letI : ExternalFuns := ops
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 8#usize })
    let s1 ← invoke "core.array.Array.index" (fun ops =>
        letI : ExternalFuns := ops
        core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC { start := 0#usize, «end» := 8#usize })
    let b ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
        letI : ExternalFuns := ops
        core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1)
    if b then
      pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongMagic)
    else
      let i1 ← invoke "Slice.index_usize" (fun ops =>
          letI : ExternalFuns := ops
          Slice.index_usize bytes 8#usize)
      if i1 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION then
        pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongVersion)
      else
        let i2 ← invoke "Slice.index_usize" (fun ops =>
            letI : ExternalFuns := ops
            Slice.index_usize bytes 9#usize)
        if i2 != 0#u8 then
          pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
        else
          let i3 ← invoke "Slice.index_usize" (fun ops =>
              letI : ExternalFuns := ops
              Slice.index_usize bytes 10#usize)
          if i3 != 0#u8 then
            pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
          else
            let i4 ← invoke "Slice.index_usize" (fun ops =>
                letI : ExternalFuns := ops
                Slice.index_usize bytes 11#usize)
            if i4 != 0#u8 then
              pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
            else
              let i5 ← invoke "Slice.index_usize" (fun ops =>
                  letI : ExternalFuns := ops
                  Slice.index_usize bytes 12#usize)
              if i5 != 0#u8 then
                pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
              else
                let i6 ← invoke "Slice.index_usize" (fun ops =>
                    letI : ExternalFuns := ops
                    Slice.index_usize bytes 13#usize)
                if i6 != 0#u8 then
                  pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                else
                  let i7 ← invoke "Slice.index_usize" (fun ops =>
                      letI : ExternalFuns := ops
                      Slice.index_usize bytes 14#usize)
                  if i7 != 0#u8 then
                    pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                  else
                    let i8 ← invoke "Slice.index_usize" (fun ops =>
                        letI : ExternalFuns := ops
                        Slice.index_usize bytes 15#usize)
                    if i8 != 0#u8 then
                      pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved)
                    else
                      let s2 ← invoke "core.slice.index.Slice.index" (fun ops =>
                          letI : ExternalFuns := ops
                          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize })
                      let a ← invoke "pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING" (fun ops =>
                          letI : ExternalFuns := ops
                          pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING)
                      let s3 ← invoke "core.array.Array.index" (fun ops =>
                          letI : ExternalFuns := ops
                          core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a { start := 0#usize, «end» := 32#usize })
                      let b1 ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
                          letI : ExternalFuns := ops
                          core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s2 s3)
                      if b1 then
                        pure (core.result.Result.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongFormatBinding)
                      else
                        let s4 ← invoke "core.slice.index.Slice.index" (fun ops =>
                            letI : ExternalFuns := ops
                            core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 128#usize, «end» := 160#usize })
                        let r ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                            letI : ExternalFuns := ops
                            core.array.TryFromSharedArraySlice.try_from 32#usize s4)
                        let a1 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                            letI : ExternalFuns := ops
                            atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r)
                        let r1 ← R1Z.PV_RJDec_Parser03.program a1
                        let r2 ← invoke "core.result.Result.map_err" (fun ops =>
                            letI : ExternalFuns := ops
                            core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r1 ())
                        let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                            letI : ExternalFuns := ops
                            core.result.Result.Insts.CoreOpsTry.branch r2)
                        match cf with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          let s5 ← invoke "core.slice.index.Slice.index" (fun ops =>
                              letI : ExternalFuns := ops
                              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 160#usize, «end» := 192#usize })
                          let r3 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                              letI : ExternalFuns := ops
                              core.array.TryFromSharedArraySlice.try_from 32#usize s5)
                          let a2 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                              letI : ExternalFuns := ops
                              atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r3)
                          let r4 ← R1Z.PV_RJDec_Parser03.program a2
                          let r5 ← invoke "core.result.Result.map_err" (fun ops =>
                              letI : ExternalFuns := ops
                              core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r4 ())
                          let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                              letI : ExternalFuns := ops
                              core.result.Result.Insts.CoreOpsTry.branch r5)
                          match cf1 with
                          | core.ops.control_flow.ControlFlow.Continue val1 =>
                            let s6 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                letI : ExternalFuns := ops
                                core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 192#usize, «end» := 224#usize })
                            let r6 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                letI : ExternalFuns := ops
                                core.array.TryFromSharedArraySlice.try_from 32#usize s6)
                            let a3 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                letI : ExternalFuns := ops
                                atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r6)
                            let r7 ← R1Z.PV_RJDec_Parser03.program a3
                            let r8 ← invoke "core.result.Result.map_err" (fun ops =>
                                letI : ExternalFuns := ops
                                core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r7 ())
                            let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                letI : ExternalFuns := ops
                                core.result.Result.Insts.CoreOpsTry.branch r8)
                            match cf2 with
                            | core.ops.control_flow.ControlFlow.Continue val2 =>
                              let s7 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                  letI : ExternalFuns := ops
                                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 224#usize, «end» := 256#usize })
                              let r9 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                  letI : ExternalFuns := ops
                                  core.array.TryFromSharedArraySlice.try_from 32#usize s7)
                              let a4 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                  letI : ExternalFuns := ops
                                  atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r9)
                              let r10 ← R1Z.PV_RJDec_Parser03.program a4
                              let r11 ← invoke "core.result.Result.map_err" (fun ops =>
                                  letI : ExternalFuns := ops
                                  core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r10 ())
                              let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                  letI : ExternalFuns := ops
                                  core.result.Result.Insts.CoreOpsTry.branch r11)
                              match cf3 with
                              | core.ops.control_flow.ControlFlow.Continue val3 =>
                                let s8 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                    letI : ExternalFuns := ops
                                    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 256#usize, «end» := 288#usize })
                                let r12 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                    letI : ExternalFuns := ops
                                    core.array.TryFromSharedArraySlice.try_from 32#usize s8)
                                let a5 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                    letI : ExternalFuns := ops
                                    atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r12)
                                let r13 ← R1Z.PV_RJDec_Parser03.program a5
                                let r14 ← invoke "core.result.Result.map_err" (fun ops =>
                                    letI : ExternalFuns := ops
                                    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r13 ())
                                let cf4 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                    letI : ExternalFuns := ops
                                    core.result.Result.Insts.CoreOpsTry.branch r14)
                                match cf4 with
                                | core.ops.control_flow.ControlFlow.Continue val4 =>
                                  let s9 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                      letI : ExternalFuns := ops
                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 288#usize, «end» := 320#usize })
                                  let r15 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                      letI : ExternalFuns := ops
                                      core.array.TryFromSharedArraySlice.try_from 32#usize s9)
                                  let a6 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                      letI : ExternalFuns := ops
                                      atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r15)
                                  let r16 ← R1Z.PV_RJDec_Parser03.program a6
                                  let r17 ← invoke "core.result.Result.map_err" (fun ops =>
                                      letI : ExternalFuns := ops
                                      core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r16 ())
                                  let cf5 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                      letI : ExternalFuns := ops
                                      core.result.Result.Insts.CoreOpsTry.branch r17)
                                  match cf5 with
                                  | core.ops.control_flow.ControlFlow.Continue val5 =>
                                    let s10 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                        letI : ExternalFuns := ops
                                        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 320#usize, «end» := 352#usize })
                                    let r18 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                        letI : ExternalFuns := ops
                                        core.array.TryFromSharedArraySlice.try_from 32#usize s10)
                                    let a7 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                        letI : ExternalFuns := ops
                                        atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r18)
                                    let r19 ← R1Z.PV_RJDec_Parser03.program a7
                                    let r20 ← invoke "core.result.Result.map_err" (fun ops =>
                                        letI : ExternalFuns := ops
                                        core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r19 ())
                                    let cf6 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                        letI : ExternalFuns := ops
                                        core.result.Result.Insts.CoreOpsTry.branch r20)
                                    match cf6 with
                                    | core.ops.control_flow.ControlFlow.Continue val6 =>
                                      let s11 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                          letI : ExternalFuns := ops
                                          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 352#usize, «end» := 384#usize })
                                      let r21 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                          letI : ExternalFuns := ops
                                          core.array.TryFromSharedArraySlice.try_from 32#usize s11)
                                      let a8 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                          letI : ExternalFuns := ops
                                          atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r21)
                                      let r22 ← R1Z.PV_RJDec_Parser03.program a8
                                      let r23 ← invoke "core.result.Result.map_err" (fun ops =>
                                          letI : ExternalFuns := ops
                                          core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r22 ())
                                      let cf7 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                          letI : ExternalFuns := ops
                                          core.result.Result.Insts.CoreOpsTry.branch r23)
                                      match cf7 with
                                      | core.ops.control_flow.ControlFlow.Continue val7 =>
                                        let s12 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                            letI : ExternalFuns := ops
                                            core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 384#usize, «end» := 416#usize })
                                        let r24 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                            letI : ExternalFuns := ops
                                            core.array.TryFromSharedArraySlice.try_from 32#usize s12)
                                        let a9 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                            letI : ExternalFuns := ops
                                            atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r24)
                                        let r25 ← R1Z.PV_RJDec_Parser03.program a9
                                        let r26 ← invoke "core.result.Result.map_err" (fun ops =>
                                            letI : ExternalFuns := ops
                                            core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r25 ())
                                        let cf8 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                            letI : ExternalFuns := ops
                                            core.result.Result.Insts.CoreOpsTry.branch r26)
                                        match cf8 with
                                        | core.ops.control_flow.ControlFlow.Continue val8 =>
                                          let s13 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                              letI : ExternalFuns := ops
                                              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 416#usize, «end» := 448#usize })
                                          let r27 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                              letI : ExternalFuns := ops
                                              core.array.TryFromSharedArraySlice.try_from 32#usize s13)
                                          let a10 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                              letI : ExternalFuns := ops
                                              atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r27)
                                          let r28 ← R1Z.PV_RJDec_Parser03.program a10
                                          let r29 ← invoke "core.result.Result.map_err" (fun ops =>
                                              letI : ExternalFuns := ops
                                              core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r28 ())
                                          let cf9 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                              letI : ExternalFuns := ops
                                              core.result.Result.Insts.CoreOpsTry.branch r29)
                                          match cf9 with
                                          | core.ops.control_flow.ControlFlow.Continue val9 =>
                                            let s14 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                letI : ExternalFuns := ops
                                                core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 448#usize, «end» := 480#usize })
                                            let r30 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                letI : ExternalFuns := ops
                                                core.array.TryFromSharedArraySlice.try_from 32#usize s14)
                                            let a11 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                letI : ExternalFuns := ops
                                                atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r30)
                                            let r31 ← R1Z.PV_RJDec_Parser03.program a11
                                            let r32 ← invoke "core.result.Result.map_err" (fun ops =>
                                                letI : ExternalFuns := ops
                                                core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r31 ())
                                            let cf10 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                letI : ExternalFuns := ops
                                                core.result.Result.Insts.CoreOpsTry.branch r32)
                                            match cf10 with
                                            | core.ops.control_flow.ControlFlow.Continue val10 =>
                                              let s15 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                  letI : ExternalFuns := ops
                                                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 480#usize, «end» := 512#usize })
                                              let r33 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                  letI : ExternalFuns := ops
                                                  core.array.TryFromSharedArraySlice.try_from 32#usize s15)
                                              let a12 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                  letI : ExternalFuns := ops
                                                  atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r33)
                                              let r34 ← R1Z.PV_RJDec_Parser03.program a12
                                              let r35 ← invoke "core.result.Result.map_err" (fun ops =>
                                                  letI : ExternalFuns := ops
                                                  core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r34 ())
                                              let cf11 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                  letI : ExternalFuns := ops
                                                  core.result.Result.Insts.CoreOpsTry.branch r35)
                                              match cf11 with
                                              | core.ops.control_flow.ControlFlow.Continue val11 =>
                                                let s16 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                    letI : ExternalFuns := ops
                                                    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 512#usize, «end» := 544#usize })
                                                let r36 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                    letI : ExternalFuns := ops
                                                    core.array.TryFromSharedArraySlice.try_from 32#usize s16)
                                                let a13 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                    letI : ExternalFuns := ops
                                                    atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r36)
                                                let r37 ← R1Z.PV_RJDec_Parser03.program a13
                                                let r38 ← invoke "core.result.Result.map_err" (fun ops =>
                                                    letI : ExternalFuns := ops
                                                    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r37 ())
                                                let cf12 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                    letI : ExternalFuns := ops
                                                    core.result.Result.Insts.CoreOpsTry.branch r38)
                                                match cf12 with
                                                | core.ops.control_flow.ControlFlow.Continue val12 =>
                                                  let s17 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                      letI : ExternalFuns := ops
                                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 544#usize, «end» := 576#usize })
                                                  let r39 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                      letI : ExternalFuns := ops
                                                      core.array.TryFromSharedArraySlice.try_from 32#usize s17)
                                                  let a14 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                      letI : ExternalFuns := ops
                                                      atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r39)
                                                  let r40 ← R1Z.PV_RJDec_Parser03.program a14
                                                  let r41 ← invoke "core.result.Result.map_err" (fun ops =>
                                                      letI : ExternalFuns := ops
                                                      core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r40 ())
                                                  let cf13 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                      letI : ExternalFuns := ops
                                                      core.result.Result.Insts.CoreOpsTry.branch r41)
                                                  match cf13 with
                                                  | core.ops.control_flow.ControlFlow.Continue val13 =>
                                                    let s18 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                        letI : ExternalFuns := ops
                                                        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 576#usize, «end» := 608#usize })
                                                    let r42 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                        letI : ExternalFuns := ops
                                                        core.array.TryFromSharedArraySlice.try_from 32#usize s18)
                                                    let a15 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                        letI : ExternalFuns := ops
                                                        atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r42)
                                                    let r43 ← R1Z.PV_RJDec_Parser03.program a15
                                                    let r44 ← invoke "core.result.Result.map_err" (fun ops =>
                                                        letI : ExternalFuns := ops
                                                        core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r43 ())
                                                    let cf14 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                        letI : ExternalFuns := ops
                                                        core.result.Result.Insts.CoreOpsTry.branch r44)
                                                    match cf14 with
                                                    | core.ops.control_flow.ControlFlow.Continue val14 =>
                                                      let s19 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                          letI : ExternalFuns := ops
                                                          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 608#usize, «end» := 640#usize })
                                                      let r45 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                          letI : ExternalFuns := ops
                                                          core.array.TryFromSharedArraySlice.try_from 32#usize s19)
                                                      let a16 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                          letI : ExternalFuns := ops
                                                          atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r45)
                                                      let r46 ← R1Z.PV_RJDec_Parser03.program a16
                                                      let r47 ← invoke "core.result.Result.map_err" (fun ops =>
                                                          letI : ExternalFuns := ops
                                                          core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r46 ())
                                                      let cf15 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                          letI : ExternalFuns := ops
                                                          core.result.Result.Insts.CoreOpsTry.branch r47)
                                                      match cf15 with
                                                      | core.ops.control_flow.ControlFlow.Continue val15 =>
                                                        let s20 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                            letI : ExternalFuns := ops
                                                            core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 640#usize, «end» := 672#usize })
                                                        let r48 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                            letI : ExternalFuns := ops
                                                            core.array.TryFromSharedArraySlice.try_from 32#usize s20)
                                                        let a17 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                            letI : ExternalFuns := ops
                                                            atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r48)
                                                        let r49 ← R1Z.PV_RJDec_Parser03.program a17
                                                        let r50 ← invoke "core.result.Result.map_err" (fun ops =>
                                                            letI : ExternalFuns := ops
                                                            core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r49 ())
                                                        let cf16 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                            letI : ExternalFuns := ops
                                                            core.result.Result.Insts.CoreOpsTry.branch r50)
                                                        match cf16 with
                                                        | core.ops.control_flow.ControlFlow.Continue val16 =>
                                                          let s21 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                              letI : ExternalFuns := ops
                                                              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 672#usize, «end» := 704#usize })
                                                          let r51 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                              letI : ExternalFuns := ops
                                                              core.array.TryFromSharedArraySlice.try_from 32#usize s21)
                                                          let a18 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                              letI : ExternalFuns := ops
                                                              atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r51)
                                                          let r52 ← R1Z.PV_RJDec_Parser03.program a18
                                                          let r53 ← invoke "core.result.Result.map_err" (fun ops =>
                                                              letI : ExternalFuns := ops
                                                              core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r52 ())
                                                          let cf17 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                              letI : ExternalFuns := ops
                                                              core.result.Result.Insts.CoreOpsTry.branch r53)
                                                          match cf17 with
                                                          | core.ops.control_flow.ControlFlow.Continue val17 =>
                                                            let s22 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                letI : ExternalFuns := ops
                                                                core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 704#usize, «end» := 736#usize })
                                                            let r54 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                                letI : ExternalFuns := ops
                                                                core.array.TryFromSharedArraySlice.try_from 32#usize s22)
                                                            let a19 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                                letI : ExternalFuns := ops
                                                                atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r54)
                                                            let r55 ← R1Z.PV_RJDec_Parser03.program a19
                                                            let r56 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                letI : ExternalFuns := ops
                                                                core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r55 ())
                                                            let cf18 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                letI : ExternalFuns := ops
                                                                core.result.Result.Insts.CoreOpsTry.branch r56)
                                                            match cf18 with
                                                            | core.ops.control_flow.ControlFlow.Continue val18 =>
                                                              let s23 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                  letI : ExternalFuns := ops
                                                                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 736#usize, «end» := 768#usize })
                                                              let r57 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                                  letI : ExternalFuns := ops
                                                                  core.array.TryFromSharedArraySlice.try_from 32#usize s23)
                                                              let a20 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                                  letI : ExternalFuns := ops
                                                                  atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r57)
                                                              let r58 ← R1Z.PV_RJDec_Parser03.program a20
                                                              let r59 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                  letI : ExternalFuns := ops
                                                                  core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r58 ())
                                                              let cf19 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                  letI : ExternalFuns := ops
                                                                  core.result.Result.Insts.CoreOpsTry.branch r59)
                                                              match cf19 with
                                                              | core.ops.control_flow.ControlFlow.Continue val19 =>
                                                                let s24 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                    letI : ExternalFuns := ops
                                                                    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 768#usize, «end» := 800#usize })
                                                                let r60 ← invoke "core.array.TryFromSharedArraySlice.try_from" (fun ops =>
                                                                    letI : ExternalFuns := ops
                                                                    core.array.TryFromSharedArraySlice.try_from 32#usize s24)
                                                                let a21 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                                    letI : ExternalFuns := ops
                                                                    atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r60)
                                                                let r61 ← R1Z.PV_RJDec_Parser03.program a21
                                                                let r62 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                    letI : ExternalFuns := ops
                                                                    core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r61 ())
                                                                let cf20 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                    letI : ExternalFuns := ops
                                                                    core.result.Result.Insts.CoreOpsTry.branch r62)
                                                                match cf20 with
                                                                | core.ops.control_flow.ControlFlow.Continue val20 =>
                                                                  let s25 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize })
                                                                  let r63 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s25)
                                                                  let a22 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r63)
                                                                  let s26 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize })
                                                                  let r64 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s26)
                                                                  let a23 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r64)
                                                                  let s27 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 120#usize })
                                                                  let r65 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s27)
                                                                  let a24 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r65)
                                                                  let i9 ← invoke "lift" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      lift (core.num.U64.from_le_bytes a24))
                                                                  let s28 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 120#usize, «end» := 128#usize })
                                                                  let r66 ← invoke "core.array.TryFromArrayCopySlice.try_from" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s28)
                                                                  let a25 ← invoke "atomic_statement.unwrap_fixed_slice" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r66)
                                                                  let i10 ← invoke "lift" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      lift (core.num.U64.from_le_bytes a25))
                                                                  let r67 ← R1Z.PV_RJDec_Parser14.program { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }
                                                                  let cf21 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      core.result.Result.Insts.CoreOpsTry.branch r67)
                                                                  match cf21 with
                                                                  | core.ops.control_flow.ControlFlow.Continue _ =>
                                                                    pure (core.result.Result.Ok { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) })
                                                                  | core.ops.control_flow.ControlFlow.Break residual =>
                                                                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                      letI : ExternalFuns := ops
                                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                                                | core.ops.control_flow.ControlFlow.Break residual =>
                                                                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                    letI : ExternalFuns := ops
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                                              | core.ops.control_flow.ControlFlow.Break residual =>
                                                                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                  letI : ExternalFuns := ops
                                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                                            | core.ops.control_flow.ControlFlow.Break residual =>
                                                              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                letI : ExternalFuns := ops
                                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                                          | core.ops.control_flow.ControlFlow.Break residual =>
                                                            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                              letI : ExternalFuns := ops
                                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                                        | core.ops.control_flow.ControlFlow.Break residual =>
                                                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                            letI : ExternalFuns := ops
                                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                                      | core.ops.control_flow.ControlFlow.Break residual =>
                                                        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                          letI : ExternalFuns := ops
                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                                      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                        letI : ExternalFuns := ops
                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                                  | core.ops.control_flow.ControlFlow.Break residual =>
                                                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                      letI : ExternalFuns := ops
                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                                | core.ops.control_flow.ControlFlow.Break residual =>
                                                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                    letI : ExternalFuns := ops
                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                              | core.ops.control_flow.ControlFlow.Break residual =>
                                                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                  letI : ExternalFuns := ops
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                            | core.ops.control_flow.ControlFlow.Break residual =>
                                              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                letI : ExternalFuns := ops
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                          | core.ops.control_flow.ControlFlow.Break residual =>
                                            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                              letI : ExternalFuns := ops
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                        | core.ops.control_flow.ControlFlow.Break residual =>
                                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                            letI : ExternalFuns := ops
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                      | core.ops.control_flow.ControlFlow.Break residual =>
                                        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                          letI : ExternalFuns := ops
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                        letI : ExternalFuns := ops
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                  | core.ops.control_flow.ControlFlow.Break residual =>
                                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                      letI : ExternalFuns := ops
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                                | core.ops.control_flow.ControlFlow.Break residual =>
                                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                    letI : ExternalFuns := ops
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                              | core.ops.control_flow.ControlFlow.Break residual =>
                                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                  letI : ExternalFuns := ops
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                            | core.ops.control_flow.ControlFlow.Break residual =>
                              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                letI : ExternalFuns := ops
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                              letI : ExternalFuns := ops
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                            letI : ExternalFuns := ops
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Slice Std.U8) :
  erase ops (program bytes) =
    pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes := by
  unfold program pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1
  try dsimp only
  try dsimp only
  apply PV_W_IfLaws.erase_if_congr
  ·
    rfl
  ·
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro s
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro s1
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro b
          try dsimp only
          apply PV_W_IfLaws.erase_if_congr
          ·
            rfl
          ·
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro i1
              try dsimp only
              apply PV_W_IfLaws.erase_if_congr
              ·
                rfl
              ·
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro i2
                  try dsimp only
                  apply PV_W_IfLaws.erase_if_congr
                  ·
                    rfl
                  ·
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro i3
                      try dsimp only
                      apply PV_W_IfLaws.erase_if_congr
                      ·
                        rfl
                      ·
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro i4
                          try dsimp only
                          apply PV_W_IfLaws.erase_if_congr
                          ·
                            rfl
                          ·
                            try dsimp only
                            rw [erase_bind]
                            apply PV_W_RecursiveLaws.bind_congr
                            ·
                              exact erase_invoke ops _ _
                            · intro i5
                              try dsimp only
                              apply PV_W_IfLaws.erase_if_congr
                              ·
                                rfl
                              ·
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro i6
                                  try dsimp only
                                  apply PV_W_IfLaws.erase_if_congr
                                  ·
                                    rfl
                                  ·
                                    try dsimp only
                                    rw [erase_bind]
                                    apply PV_W_RecursiveLaws.bind_congr
                                    ·
                                      exact erase_invoke ops _ _
                                    · intro i7
                                      try dsimp only
                                      apply PV_W_IfLaws.erase_if_congr
                                      ·
                                        rfl
                                      ·
                                        try dsimp only
                                        rw [erase_bind]
                                        apply PV_W_RecursiveLaws.bind_congr
                                        ·
                                          exact erase_invoke ops _ _
                                        · intro i8
                                          try dsimp only
                                          apply PV_W_IfLaws.erase_if_congr
                                          ·
                                            rfl
                                          ·
                                            try dsimp only
                                            rw [erase_bind]
                                            apply PV_W_RecursiveLaws.bind_congr
                                            ·
                                              exact erase_invoke ops _ _
                                            · intro s2
                                              try dsimp only
                                              rw [erase_bind]
                                              apply PV_W_RecursiveLaws.bind_congr
                                              ·
                                                exact erase_invoke ops _ _
                                              · intro a
                                                try dsimp only
                                                rw [erase_bind]
                                                apply PV_W_RecursiveLaws.bind_congr
                                                ·
                                                  exact erase_invoke ops _ _
                                                · intro s3
                                                  try dsimp only
                                                  rw [erase_bind]
                                                  apply PV_W_RecursiveLaws.bind_congr
                                                  ·
                                                    exact erase_invoke ops _ _
                                                  · intro b1
                                                    try dsimp only
                                                    apply PV_W_IfLaws.erase_if_congr
                                                    ·
                                                      rfl
                                                    ·
                                                      try dsimp only
                                                      rw [erase_bind]
                                                      apply PV_W_RecursiveLaws.bind_congr
                                                      ·
                                                        exact erase_invoke ops _ _
                                                      · intro s4
                                                        try dsimp only
                                                        rw [erase_bind]
                                                        apply PV_W_RecursiveLaws.bind_congr
                                                        ·
                                                          exact erase_invoke ops _ _
                                                        · intro r
                                                          try dsimp only
                                                          rw [erase_bind]
                                                          apply PV_W_RecursiveLaws.bind_congr
                                                          ·
                                                            exact erase_invoke ops _ _
                                                          · intro a1
                                                            try dsimp only
                                                            rw [erase_bind]
                                                            apply PV_W_RecursiveLaws.bind_congr
                                                            ·
                                                              exact R1Z.PV_RJDec_Parser03.source ops a1
                                                            · intro r1
                                                              try dsimp only
                                                              rw [erase_bind]
                                                              apply PV_W_RecursiveLaws.bind_congr
                                                              ·
                                                                exact erase_invoke ops _ _
                                                              · intro r2
                                                                try dsimp only
                                                                rw [erase_bind]
                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                ·
                                                                  exact erase_invoke ops _ _
                                                                · intro cf
                                                                  try dsimp only
                                                                  cases cf with
                                                                  | Continue val =>
                                                                    try dsimp only
                                                                    rw [erase_bind]
                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                    ·
                                                                      exact erase_invoke ops _ _
                                                                    · intro s5
                                                                      try dsimp only
                                                                      rw [erase_bind]
                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                      ·
                                                                        exact erase_invoke ops _ _
                                                                      · intro r3
                                                                        try dsimp only
                                                                        rw [erase_bind]
                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                        ·
                                                                          exact erase_invoke ops _ _
                                                                        · intro a2
                                                                          try dsimp only
                                                                          rw [erase_bind]
                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                          ·
                                                                            exact R1Z.PV_RJDec_Parser03.source ops a2
                                                                          · intro r4
                                                                            try dsimp only
                                                                            rw [erase_bind]
                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                            ·
                                                                              exact erase_invoke ops _ _
                                                                            · intro r5
                                                                              try dsimp only
                                                                              rw [erase_bind]
                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                              ·
                                                                                exact erase_invoke ops _ _
                                                                              · intro cf1
                                                                                try dsimp only
                                                                                cases cf1 with
                                                                                | Continue val1 =>
                                                                                  try dsimp only
                                                                                  rw [erase_bind]
                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                  ·
                                                                                    exact erase_invoke ops _ _
                                                                                  · intro s6
                                                                                    try dsimp only
                                                                                    rw [erase_bind]
                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                    ·
                                                                                      exact erase_invoke ops _ _
                                                                                    · intro r6
                                                                                      try dsimp only
                                                                                      rw [erase_bind]
                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                      ·
                                                                                        exact erase_invoke ops _ _
                                                                                      · intro a3
                                                                                        try dsimp only
                                                                                        rw [erase_bind]
                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                        ·
                                                                                          exact R1Z.PV_RJDec_Parser03.source ops a3
                                                                                        · intro r7
                                                                                          try dsimp only
                                                                                          rw [erase_bind]
                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                          ·
                                                                                            exact erase_invoke ops _ _
                                                                                          · intro r8
                                                                                            try dsimp only
                                                                                            rw [erase_bind]
                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                            ·
                                                                                              exact erase_invoke ops _ _
                                                                                            · intro cf2
                                                                                              try dsimp only
                                                                                              cases cf2 with
                                                                                              | Continue val2 =>
                                                                                                try dsimp only
                                                                                                rw [erase_bind]
                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                ·
                                                                                                  exact erase_invoke ops _ _
                                                                                                · intro s7
                                                                                                  try dsimp only
                                                                                                  rw [erase_bind]
                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                  ·
                                                                                                    exact erase_invoke ops _ _
                                                                                                  · intro r9
                                                                                                    try dsimp only
                                                                                                    rw [erase_bind]
                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                    ·
                                                                                                      exact erase_invoke ops _ _
                                                                                                    · intro a4
                                                                                                      try dsimp only
                                                                                                      rw [erase_bind]
                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                      ·
                                                                                                        exact R1Z.PV_RJDec_Parser03.source ops a4
                                                                                                      · intro r10
                                                                                                        try dsimp only
                                                                                                        rw [erase_bind]
                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                        ·
                                                                                                          exact erase_invoke ops _ _
                                                                                                        · intro r11
                                                                                                          try dsimp only
                                                                                                          rw [erase_bind]
                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                          ·
                                                                                                            exact erase_invoke ops _ _
                                                                                                          · intro cf3
                                                                                                            try dsimp only
                                                                                                            cases cf3 with
                                                                                                            | Continue val3 =>
                                                                                                              try dsimp only
                                                                                                              rw [erase_bind]
                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                              ·
                                                                                                                exact erase_invoke ops _ _
                                                                                                              · intro s8
                                                                                                                try dsimp only
                                                                                                                rw [erase_bind]
                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                ·
                                                                                                                  exact erase_invoke ops _ _
                                                                                                                · intro r12
                                                                                                                  try dsimp only
                                                                                                                  rw [erase_bind]
                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                  ·
                                                                                                                    exact erase_invoke ops _ _
                                                                                                                  · intro a5
                                                                                                                    try dsimp only
                                                                                                                    rw [erase_bind]
                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                    ·
                                                                                                                      exact R1Z.PV_RJDec_Parser03.source ops a5
                                                                                                                    · intro r13
                                                                                                                      try dsimp only
                                                                                                                      rw [erase_bind]
                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                      ·
                                                                                                                        exact erase_invoke ops _ _
                                                                                                                      · intro r14
                                                                                                                        try dsimp only
                                                                                                                        rw [erase_bind]
                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                        ·
                                                                                                                          exact erase_invoke ops _ _
                                                                                                                        · intro cf4
                                                                                                                          try dsimp only
                                                                                                                          cases cf4 with
                                                                                                                          | Continue val4 =>
                                                                                                                            try dsimp only
                                                                                                                            rw [erase_bind]
                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                            ·
                                                                                                                              exact erase_invoke ops _ _
                                                                                                                            · intro s9
                                                                                                                              try dsimp only
                                                                                                                              rw [erase_bind]
                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                              ·
                                                                                                                                exact erase_invoke ops _ _
                                                                                                                              · intro r15
                                                                                                                                try dsimp only
                                                                                                                                rw [erase_bind]
                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                ·
                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                · intro a6
                                                                                                                                  try dsimp only
                                                                                                                                  rw [erase_bind]
                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                  ·
                                                                                                                                    exact R1Z.PV_RJDec_Parser03.source ops a6
                                                                                                                                  · intro r16
                                                                                                                                    try dsimp only
                                                                                                                                    rw [erase_bind]
                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                    ·
                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                    · intro r17
                                                                                                                                      try dsimp only
                                                                                                                                      rw [erase_bind]
                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                      ·
                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                      · intro cf5
                                                                                                                                        try dsimp only
                                                                                                                                        cases cf5 with
                                                                                                                                        | Continue val5 =>
                                                                                                                                          try dsimp only
                                                                                                                                          rw [erase_bind]
                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                          ·
                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                          · intro s10
                                                                                                                                            try dsimp only
                                                                                                                                            rw [erase_bind]
                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                            ·
                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                            · intro r18
                                                                                                                                              try dsimp only
                                                                                                                                              rw [erase_bind]
                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                              ·
                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                              · intro a7
                                                                                                                                                try dsimp only
                                                                                                                                                rw [erase_bind]
                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                ·
                                                                                                                                                  exact R1Z.PV_RJDec_Parser03.source ops a7
                                                                                                                                                · intro r19
                                                                                                                                                  try dsimp only
                                                                                                                                                  rw [erase_bind]
                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                  ·
                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                  · intro r20
                                                                                                                                                    try dsimp only
                                                                                                                                                    rw [erase_bind]
                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                    ·
                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                    · intro cf6
                                                                                                                                                      try dsimp only
                                                                                                                                                      cases cf6 with
                                                                                                                                                      | Continue val6 =>
                                                                                                                                                        try dsimp only
                                                                                                                                                        rw [erase_bind]
                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                        ·
                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                        · intro s11
                                                                                                                                                          try dsimp only
                                                                                                                                                          rw [erase_bind]
                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                          ·
                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                          · intro r21
                                                                                                                                                            try dsimp only
                                                                                                                                                            rw [erase_bind]
                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                            ·
                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                            · intro a8
                                                                                                                                                              try dsimp only
                                                                                                                                                              rw [erase_bind]
                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                              ·
                                                                                                                                                                exact R1Z.PV_RJDec_Parser03.source ops a8
                                                                                                                                                              · intro r22
                                                                                                                                                                try dsimp only
                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                ·
                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                · intro r23
                                                                                                                                                                  try dsimp only
                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                  ·
                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                  · intro cf7
                                                                                                                                                                    try dsimp only
                                                                                                                                                                    cases cf7 with
                                                                                                                                                                    | Continue val7 =>
                                                                                                                                                                      try dsimp only
                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                      ·
                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                      · intro s12
                                                                                                                                                                        try dsimp only
                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                        ·
                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                        · intro r24
                                                                                                                                                                          try dsimp only
                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                          ·
                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                          · intro a9
                                                                                                                                                                            try dsimp only
                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                            ·
                                                                                                                                                                              exact R1Z.PV_RJDec_Parser03.source ops a9
                                                                                                                                                                            · intro r25
                                                                                                                                                                              try dsimp only
                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                              ·
                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                              · intro r26
                                                                                                                                                                                try dsimp only
                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                ·
                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                · intro cf8
                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                  cases cf8 with
                                                                                                                                                                                  | Continue val8 =>
                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                    ·
                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                    · intro s13
                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                      ·
                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                      · intro r27
                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                        ·
                                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                                        · intro a10
                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                          ·
                                                                                                                                                                                            exact R1Z.PV_RJDec_Parser03.source ops a10
                                                                                                                                                                                          · intro r28
                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                            ·
                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                            · intro r29
                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                              ·
                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                              · intro cf9
                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                cases cf9 with
                                                                                                                                                                                                | Continue val9 =>
                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                  · intro s14
                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                                    · intro r30
                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                      · intro a11
                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                        ·
                                                                                                                                                                                                          exact R1Z.PV_RJDec_Parser03.source ops a11
                                                                                                                                                                                                        · intro r31
                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                          ·
                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                          · intro r32
                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                            ·
                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                            · intro cf10
                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                              cases cf10 with
                                                                                                                                                                                                              | Continue val10 =>
                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                ·
                                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                                                · intro s15
                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                  · intro r33
                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                                                    · intro a12
                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                        exact R1Z.PV_RJDec_Parser03.source ops a12
                                                                                                                                                                                                                      · intro r34
                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                                                                        · intro r35
                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                                          · intro cf11
                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                            cases cf11 with
                                                                                                                                                                                                                            | Continue val11 =>
                                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                                                              · intro s16
                                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                                                                · intro r36
                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                  · intro a13
                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                      exact R1Z.PV_RJDec_Parser03.source ops a13
                                                                                                                                                                                                                                    · intro r37
                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                                                      · intro r38
                                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                                                                                        · intro cf12
                                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                                          cases cf12 with
                                                                                                                                                                                                                                          | Continue val12 =>
                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                                                            · intro s17
                                                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                                                                              · intro r39
                                                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                                                                                · intro a14
                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                    exact R1Z.PV_RJDec_Parser03.source ops a14
                                                                                                                                                                                                                                                  · intro r40
                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                                                                                    · intro r41
                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                                                                      · intro cf13
                                                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                                                        cases cf13 with
                                                                                                                                                                                                                                                        | Continue val13 =>
                                                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                                                                          · intro s18
                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                                                                            · intro r42
                                                                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                                                                                              · intro a15
                                                                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                  exact R1Z.PV_RJDec_Parser03.source ops a15
                                                                                                                                                                                                                                                                · intro r43
                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                  · intro r44
                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                    · intro cf14
                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                      cases cf14 with
                                                                                                                                                                                                                                                                      | Continue val14 =>
                                                                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                        · intro s19
                                                                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                          · intro r45
                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                            · intro a16
                                                                                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                exact R1Z.PV_RJDec_Parser03.source ops a16
                                                                                                                                                                                                                                                                              · intro r46
                                                                                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                · intro r47
                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                  · intro cf15
                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                    cases cf15 with
                                                                                                                                                                                                                                                                                    | Continue val15 =>
                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                      · intro s20
                                                                                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                        · intro r48
                                                                                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                          · intro a17
                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                              exact R1Z.PV_RJDec_Parser03.source ops a17
                                                                                                                                                                                                                                                                                            · intro r49
                                                                                                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                              · intro r50
                                                                                                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                · intro cf16
                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                  cases cf16 with
                                                                                                                                                                                                                                                                                                  | Continue val16 =>
                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                    · intro s21
                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                      · intro r51
                                                                                                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                        · intro a18
                                                                                                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                            exact R1Z.PV_RJDec_Parser03.source ops a18
                                                                                                                                                                                                                                                                                                          · intro r52
                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                            · intro r53
                                                                                                                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                              · intro cf17
                                                                                                                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                                                                                                                cases cf17 with
                                                                                                                                                                                                                                                                                                                | Continue val17 =>
                                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                  · intro s22
                                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                    · intro r54
                                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                      · intro a19
                                                                                                                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                          exact R1Z.PV_RJDec_Parser03.source ops a19
                                                                                                                                                                                                                                                                                                                        · intro r55
                                                                                                                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                          · intro r56
                                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                            · intro cf18
                                                                                                                                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                                                                                                                                              cases cf18 with
                                                                                                                                                                                                                                                                                                                              | Continue val18 =>
                                                                                                                                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                · intro s23
                                                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                  · intro r57
                                                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                    · intro a20
                                                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                        exact R1Z.PV_RJDec_Parser03.source ops a20
                                                                                                                                                                                                                                                                                                                                      · intro r58
                                                                                                                                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                        · intro r59
                                                                                                                                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                          · intro cf19
                                                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                                                            cases cf19 with
                                                                                                                                                                                                                                                                                                                                            | Continue val19 =>
                                                                                                                                                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                              · intro s24
                                                                                                                                                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                · intro r60
                                                                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                  · intro a21
                                                                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                                      exact R1Z.PV_RJDec_Parser03.source ops a21
                                                                                                                                                                                                                                                                                                                                                    · intro r61
                                                                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                      · intro r62
                                                                                                                                                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                        · intro cf20
                                                                                                                                                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                                                                                                                                                          cases cf20 with
                                                                                                                                                                                                                                                                                                                                                          | Continue val20 =>
                                                                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                            · intro s25
                                                                                                                                                                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                              · intro r63
                                                                                                                                                                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                · intro a22
                                                                                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                  · intro s26
                                                                                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                    · intro r64
                                                                                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                      · intro a23
                                                                                                                                                                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                        · intro s27
                                                                                                                                                                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                          · intro r65
                                                                                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                                                                                            rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                            apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                            · intro a24
                                                                                                                                                                                                                                                                                                                                                                              try dsimp only
                                                                                                                                                                                                                                                                                                                                                                              rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                              apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                              · intro i9
                                                                                                                                                                                                                                                                                                                                                                                try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                                apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                                · intro s28
                                                                                                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                                  · intro r66
                                                                                                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                    rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                                    apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                                    · intro a25
                                                                                                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                                      · intro i10
                                                                                                                                                                                                                                                                                                                                                                                        try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                        rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                                        apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                                                                          exact R1Z.PV_RJDec_Parser14.source ops { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }
                                                                                                                                                                                                                                                                                                                                                                                        · intro r67
                                                                                                                                                                                                                                                                                                                                                                                          try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                          rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                                          apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                                          · intro cf21
                                                                                                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                            cases cf21 with
                                                                                                                                                                                                                                                                                                                                                                                            | Continue unused0_0 =>
                                                                                                                                                                                                                                                                                                                                                                                              rfl
                                                                                                                                                                                                                                                                                                                                                                                            | Break residual =>
                                                                                                                                                                                                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                          | Break residual =>
                                                                                                                                                                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                            | Break residual =>
                                                                                                                                                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                              | Break residual =>
                                                                                                                                                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                | Break residual =>
                                                                                                                                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                  | Break residual =>
                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                    | Break residual =>
                                                                                                                                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                      | Break residual =>
                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                                                                        | Break residual =>
                                                                                                                                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                                                                                                                                          | Break residual =>
                                                                                                                                                                                                                                            exact erase_invoke ops _ _
                                                                                                                                                                                                                            | Break residual =>
                                                                                                                                                                                                                              exact erase_invoke ops _ _
                                                                                                                                                                                                              | Break residual =>
                                                                                                                                                                                                                exact erase_invoke ops _ _
                                                                                                                                                                                                | Break residual =>
                                                                                                                                                                                                  exact erase_invoke ops _ _
                                                                                                                                                                                  | Break residual =>
                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                    | Break residual =>
                                                                                                                                                                      exact erase_invoke ops _ _
                                                                                                                                                      | Break residual =>
                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                        | Break residual =>
                                                                                                                                          exact erase_invoke ops _ _
                                                                                                                          | Break residual =>
                                                                                                                            exact erase_invoke ops _ _
                                                                                                            | Break residual =>
                                                                                                              exact erase_invoke ops _ _
                                                                                              | Break residual =>
                                                                                                exact erase_invoke ops _ _
                                                                                | Break residual =>
                                                                                  exact erase_invoke ops _ _
                                                                  | Break residual =>
                                                                    exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_ParserR12
