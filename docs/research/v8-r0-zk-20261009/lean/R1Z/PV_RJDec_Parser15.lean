import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Parser15
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (bytes : Slice Std.U8) :
  P (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let i := Slice.len bytes
  let i1 ← invoke "pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES)
  if i != i1 then
    pure (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongLength)
  else
    let s ← invoke "core.slice.index.Slice.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 4#usize })
    let s1 ← invoke "core.array.Array.index" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC { start := 0#usize, «end» := 4#usize })
    let b ← invoke "core.cmp.PartialEq.ne.trait_default" (fun ops =>
        letI : ProverRwFull.ExternalFuns := ops
        core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1)
    if b then
      pure (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongMagic)
    else
      let i2 ← invoke "Slice.index_usize" (fun ops =>
          letI : ProverRwFull.ExternalFuns := ops
          Slice.index_usize bytes 4#usize)
      if i2 != pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION then
        pure (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongVersion)
      else
        let i3 ← invoke "Slice.index_usize" (fun ops =>
            letI : ProverRwFull.ExternalFuns := ops
            Slice.index_usize bytes 5#usize)
        if i3 != pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION then
          pure (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongPairFormat)
        else
          let i4 ← invoke "Slice.index_usize" (fun ops =>
              letI : ProverRwFull.ExternalFuns := ops
              Slice.index_usize bytes 6#usize)
          if i4 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION then
            pure (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongDigestEncoding)
          else
            let i5 ← invoke "Slice.index_usize" (fun ops =>
                letI : ProverRwFull.ExternalFuns := ops
                Slice.index_usize bytes 7#usize)
            if i5 != 1#u8 then
              pure (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongSuccessCode)
            else
              let s2 ← invoke "core.slice.index.Slice.index" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize })
              let r ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  pool_v1.pair_terminal.exact 32#usize s2)
              let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTry.branch r)
              match cf with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r1 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    atomic_statement.decode_digest_canonical val)
                let r2 ← invoke "core.result.Result.map_err" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r1 ())
                let cf1 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTry.branch r2)
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val1 =>
                  let s3 ← invoke "core.slice.index.Slice.index" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize })
                  let r3 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      pool_v1.pair_terminal.exact 32#usize s3)
                  let cf2 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      core.result.Result.Insts.CoreOpsTry.branch r3)
                  match cf2 with
                  | core.ops.control_flow.ControlFlow.Continue val2 =>
                    let r4 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                        letI : ProverRwFull.ExternalFuns := ops
                        atomic_statement.decode_digest_canonical val2)
                    let r5 ← invoke "core.result.Result.map_err" (fun ops =>
                        letI : ProverRwFull.ExternalFuns := ops
                        core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r4 ())
                    let cf3 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                        letI : ProverRwFull.ExternalFuns := ops
                        core.result.Result.Insts.CoreOpsTry.branch r5)
                    match cf3 with
                    | core.ops.control_flow.ControlFlow.Continue val3 =>
                      let s4 ← invoke "core.slice.index.Slice.index" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize })
                      let r6 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          pool_v1.pair_terminal.exact 32#usize s4)
                      let cf4 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          core.result.Result.Insts.CoreOpsTry.branch r6)
                      match cf4 with
                      | core.ops.control_flow.ControlFlow.Continue val4 =>
                        let r7 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            atomic_statement.decode_digest_canonical val4)
                        let r8 ← invoke "core.result.Result.map_err" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r7 ())
                        let cf5 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.Insts.CoreOpsTry.branch r8)
                        match cf5 with
                        | core.ops.control_flow.ControlFlow.Continue val5 =>
                          let s5 ← invoke "core.slice.index.Slice.index" (fun ops =>
                              letI : ProverRwFull.ExternalFuns := ops
                              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 144#usize })
                          let r9 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                              letI : ProverRwFull.ExternalFuns := ops
                              pool_v1.pair_terminal.exact 32#usize s5)
                          let cf6 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                              letI : ProverRwFull.ExternalFuns := ops
                              core.result.Result.Insts.CoreOpsTry.branch r9)
                          match cf6 with
                          | core.ops.control_flow.ControlFlow.Continue val6 =>
                            let r10 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                atomic_statement.decode_digest_canonical val6)
                            let r11 ← invoke "core.result.Result.map_err" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r10 ())
                            let cf7 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                core.result.Result.Insts.CoreOpsTry.branch r11)
                            match cf7 with
                            | core.ops.control_flow.ControlFlow.Continue val7 =>
                              let s6 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                  letI : ProverRwFull.ExternalFuns := ops
                                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 144#usize, «end» := 176#usize })
                              let r12 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                  letI : ProverRwFull.ExternalFuns := ops
                                  pool_v1.pair_terminal.exact 32#usize s6)
                              let cf8 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                  letI : ProverRwFull.ExternalFuns := ops
                                  core.result.Result.Insts.CoreOpsTry.branch r12)
                              match cf8 with
                              | core.ops.control_flow.ControlFlow.Continue val8 =>
                                let r13 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                    letI : ProverRwFull.ExternalFuns := ops
                                    atomic_statement.decode_digest_canonical val8)
                                let r14 ← invoke "core.result.Result.map_err" (fun ops =>
                                    letI : ProverRwFull.ExternalFuns := ops
                                    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r13 ())
                                let cf9 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                    letI : ProverRwFull.ExternalFuns := ops
                                    core.result.Result.Insts.CoreOpsTry.branch r14)
                                match cf9 with
                                | core.ops.control_flow.ControlFlow.Continue val9 =>
                                  let s7 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                      letI : ProverRwFull.ExternalFuns := ops
                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 176#usize, «end» := 208#usize })
                                  let r15 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                      letI : ProverRwFull.ExternalFuns := ops
                                      pool_v1.pair_terminal.exact 32#usize s7)
                                  let cf10 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                      letI : ProverRwFull.ExternalFuns := ops
                                      core.result.Result.Insts.CoreOpsTry.branch r15)
                                  match cf10 with
                                  | core.ops.control_flow.ControlFlow.Continue val10 =>
                                    let r16 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                        letI : ProverRwFull.ExternalFuns := ops
                                        atomic_statement.decode_digest_canonical val10)
                                    let r17 ← invoke "core.result.Result.map_err" (fun ops =>
                                        letI : ProverRwFull.ExternalFuns := ops
                                        core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r16 ())
                                    let cf11 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                        letI : ProverRwFull.ExternalFuns := ops
                                        core.result.Result.Insts.CoreOpsTry.branch r17)
                                    match cf11 with
                                    | core.ops.control_flow.ControlFlow.Continue val11 =>
                                      let s8 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                          letI : ProverRwFull.ExternalFuns := ops
                                          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 208#usize, «end» := 240#usize })
                                      let r18 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                          letI : ProverRwFull.ExternalFuns := ops
                                          pool_v1.pair_terminal.exact 32#usize s8)
                                      let cf12 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                          letI : ProverRwFull.ExternalFuns := ops
                                          core.result.Result.Insts.CoreOpsTry.branch r18)
                                      match cf12 with
                                      | core.ops.control_flow.ControlFlow.Continue val12 =>
                                        let r19 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                            letI : ProverRwFull.ExternalFuns := ops
                                            atomic_statement.decode_digest_canonical val12)
                                        let r20 ← invoke "core.result.Result.map_err" (fun ops =>
                                            letI : ProverRwFull.ExternalFuns := ops
                                            core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r19 ())
                                        let cf13 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                            letI : ProverRwFull.ExternalFuns := ops
                                            core.result.Result.Insts.CoreOpsTry.branch r20)
                                        match cf13 with
                                        | core.ops.control_flow.ControlFlow.Continue val13 =>
                                          let s9 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                              letI : ProverRwFull.ExternalFuns := ops
                                              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 240#usize, «end» := 272#usize })
                                          let r21 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                              letI : ProverRwFull.ExternalFuns := ops
                                              pool_v1.pair_terminal.exact 32#usize s9)
                                          let cf14 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                              letI : ProverRwFull.ExternalFuns := ops
                                              core.result.Result.Insts.CoreOpsTry.branch r21)
                                          match cf14 with
                                          | core.ops.control_flow.ControlFlow.Continue val14 =>
                                            let r22 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                letI : ProverRwFull.ExternalFuns := ops
                                                atomic_statement.decode_digest_canonical val14)
                                            let r23 ← invoke "core.result.Result.map_err" (fun ops =>
                                                letI : ProverRwFull.ExternalFuns := ops
                                                core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r22 ())
                                            let cf15 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                letI : ProverRwFull.ExternalFuns := ops
                                                core.result.Result.Insts.CoreOpsTry.branch r23)
                                            match cf15 with
                                            | core.ops.control_flow.ControlFlow.Continue val15 =>
                                              let s10 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                  letI : ProverRwFull.ExternalFuns := ops
                                                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 272#usize, «end» := 304#usize })
                                              let r24 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                  letI : ProverRwFull.ExternalFuns := ops
                                                  pool_v1.pair_terminal.exact 32#usize s10)
                                              let cf16 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                  letI : ProverRwFull.ExternalFuns := ops
                                                  core.result.Result.Insts.CoreOpsTry.branch r24)
                                              match cf16 with
                                              | core.ops.control_flow.ControlFlow.Continue val16 =>
                                                let r25 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                    letI : ProverRwFull.ExternalFuns := ops
                                                    atomic_statement.decode_digest_canonical val16)
                                                let r26 ← invoke "core.result.Result.map_err" (fun ops =>
                                                    letI : ProverRwFull.ExternalFuns := ops
                                                    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r25 ())
                                                let cf17 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                    letI : ProverRwFull.ExternalFuns := ops
                                                    core.result.Result.Insts.CoreOpsTry.branch r26)
                                                match cf17 with
                                                | core.ops.control_flow.ControlFlow.Continue val17 =>
                                                  let s11 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                      letI : ProverRwFull.ExternalFuns := ops
                                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 304#usize, «end» := 336#usize })
                                                  let r27 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                      letI : ProverRwFull.ExternalFuns := ops
                                                      pool_v1.pair_terminal.exact 32#usize s11)
                                                  let cf18 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                      letI : ProverRwFull.ExternalFuns := ops
                                                      core.result.Result.Insts.CoreOpsTry.branch r27)
                                                  match cf18 with
                                                  | core.ops.control_flow.ControlFlow.Continue val18 =>
                                                    let r28 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                        letI : ProverRwFull.ExternalFuns := ops
                                                        atomic_statement.decode_digest_canonical val18)
                                                    let r29 ← invoke "core.result.Result.map_err" (fun ops =>
                                                        letI : ProverRwFull.ExternalFuns := ops
                                                        core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r28 ())
                                                    let cf19 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                        letI : ProverRwFull.ExternalFuns := ops
                                                        core.result.Result.Insts.CoreOpsTry.branch r29)
                                                    match cf19 with
                                                    | core.ops.control_flow.ControlFlow.Continue val19 =>
                                                      let s12 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                          letI : ProverRwFull.ExternalFuns := ops
                                                          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 336#usize, «end» := 368#usize })
                                                      let r30 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                          letI : ProverRwFull.ExternalFuns := ops
                                                          pool_v1.pair_terminal.exact 32#usize s12)
                                                      let cf20 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                          letI : ProverRwFull.ExternalFuns := ops
                                                          core.result.Result.Insts.CoreOpsTry.branch r30)
                                                      match cf20 with
                                                      | core.ops.control_flow.ControlFlow.Continue val20 =>
                                                        let r31 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                            letI : ProverRwFull.ExternalFuns := ops
                                                            atomic_statement.decode_digest_canonical val20)
                                                        let r32 ← invoke "core.result.Result.map_err" (fun ops =>
                                                            letI : ProverRwFull.ExternalFuns := ops
                                                            core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r31 ())
                                                        let cf21 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                            letI : ProverRwFull.ExternalFuns := ops
                                                            core.result.Result.Insts.CoreOpsTry.branch r32)
                                                        match cf21 with
                                                        | core.ops.control_flow.ControlFlow.Continue val21 =>
                                                          let s13 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                              letI : ProverRwFull.ExternalFuns := ops
                                                              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 368#usize, «end» := 400#usize })
                                                          let r33 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                              letI : ProverRwFull.ExternalFuns := ops
                                                              pool_v1.pair_terminal.exact 32#usize s13)
                                                          let cf22 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                              letI : ProverRwFull.ExternalFuns := ops
                                                              core.result.Result.Insts.CoreOpsTry.branch r33)
                                                          match cf22 with
                                                          | core.ops.control_flow.ControlFlow.Continue val22 =>
                                                            let r34 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                atomic_statement.decode_digest_canonical val22)
                                                            let r35 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r34 ())
                                                            let cf23 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                core.result.Result.Insts.CoreOpsTry.branch r35)
                                                            match cf23 with
                                                            | core.ops.control_flow.ControlFlow.Continue val23 =>
                                                              let s14 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 400#usize, «end» := 432#usize })
                                                              let r36 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                  pool_v1.pair_terminal.exact 32#usize s14)
                                                              let cf24 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                  core.result.Result.Insts.CoreOpsTry.branch r36)
                                                              match cf24 with
                                                              | core.ops.control_flow.ControlFlow.Continue val24 =>
                                                                let r37 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                    atomic_statement.decode_digest_canonical val24)
                                                                let r38 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r37 ())
                                                                let cf25 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                    core.result.Result.Insts.CoreOpsTry.branch r38)
                                                                match cf25 with
                                                                | core.ops.control_flow.ControlFlow.Continue val25 =>
                                                                  let s15 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 432#usize, «end» := 464#usize })
                                                                  let r39 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                      pool_v1.pair_terminal.exact 32#usize s15)
                                                                  let cf26 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                      core.result.Result.Insts.CoreOpsTry.branch r39)
                                                                  match cf26 with
                                                                  | core.ops.control_flow.ControlFlow.Continue val26 =>
                                                                    let r40 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                        atomic_statement.decode_digest_canonical val26)
                                                                    let r41 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                        core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r40 ())
                                                                    let cf27 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                        core.result.Result.Insts.CoreOpsTry.branch r41)
                                                                    match cf27 with
                                                                    | core.ops.control_flow.ControlFlow.Continue val27 =>
                                                                      let s16 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                          letI : ProverRwFull.ExternalFuns := ops
                                                                          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 464#usize, «end» := 496#usize })
                                                                      let r42 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                                          letI : ProverRwFull.ExternalFuns := ops
                                                                          pool_v1.pair_terminal.exact 32#usize s16)
                                                                      let cf28 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                          letI : ProverRwFull.ExternalFuns := ops
                                                                          core.result.Result.Insts.CoreOpsTry.branch r42)
                                                                      match cf28 with
                                                                      | core.ops.control_flow.ControlFlow.Continue val28 =>
                                                                        let r43 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                                            letI : ProverRwFull.ExternalFuns := ops
                                                                            atomic_statement.decode_digest_canonical val28)
                                                                        let r44 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                            letI : ProverRwFull.ExternalFuns := ops
                                                                            core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r43 ())
                                                                        let cf29 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                            letI : ProverRwFull.ExternalFuns := ops
                                                                            core.result.Result.Insts.CoreOpsTry.branch r44)
                                                                        match cf29 with
                                                                        | core.ops.control_flow.ControlFlow.Continue val29 =>
                                                                          let s17 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                              letI : ProverRwFull.ExternalFuns := ops
                                                                              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 496#usize, «end» := 528#usize })
                                                                          let r45 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                                              letI : ProverRwFull.ExternalFuns := ops
                                                                              pool_v1.pair_terminal.exact 32#usize s17)
                                                                          let cf30 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                              letI : ProverRwFull.ExternalFuns := ops
                                                                              core.result.Result.Insts.CoreOpsTry.branch r45)
                                                                          match cf30 with
                                                                          | core.ops.control_flow.ControlFlow.Continue val30 =>
                                                                            let r46 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                                atomic_statement.decode_digest_canonical val30)
                                                                            let r47 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                                core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r46 ())
                                                                            let cf31 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                                core.result.Result.Insts.CoreOpsTry.branch r47)
                                                                            match cf31 with
                                                                            | core.ops.control_flow.ControlFlow.Continue val31 =>
                                                                              let s18 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 528#usize, «end» := 560#usize })
                                                                              let r48 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                                  pool_v1.pair_terminal.exact 32#usize s18)
                                                                              let cf32 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                                  core.result.Result.Insts.CoreOpsTry.branch r48)
                                                                              match cf32 with
                                                                              | core.ops.control_flow.ControlFlow.Continue val32 =>
                                                                                let r49 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                                    atomic_statement.decode_digest_canonical val32)
                                                                                let r50 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                                    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r49 ())
                                                                                let cf33 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                                    core.result.Result.Insts.CoreOpsTry.branch r50)
                                                                                match cf33 with
                                                                                | core.ops.control_flow.ControlFlow.Continue val33 =>
                                                                                  let s19 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 560#usize, «end» := 592#usize })
                                                                                  let r51 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                                      pool_v1.pair_terminal.exact 32#usize s19)
                                                                                  let cf34 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                                      core.result.Result.Insts.CoreOpsTry.branch r51)
                                                                                  match cf34 with
                                                                                  | core.ops.control_flow.ControlFlow.Continue val34 =>
                                                                                    let r52 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                                        atomic_statement.decode_digest_canonical val34)
                                                                                    let r53 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                                        core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r52 ())
                                                                                    let cf35 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                                        core.result.Result.Insts.CoreOpsTry.branch r53)
                                                                                    match cf35 with
                                                                                    | core.ops.control_flow.ControlFlow.Continue val35 =>
                                                                                      let s20 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                                          letI : ProverRwFull.ExternalFuns := ops
                                                                                          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 592#usize, «end» := 624#usize })
                                                                                      let r54 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                                                          letI : ProverRwFull.ExternalFuns := ops
                                                                                          pool_v1.pair_terminal.exact 32#usize s20)
                                                                                      let cf36 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                          letI : ProverRwFull.ExternalFuns := ops
                                                                                          core.result.Result.Insts.CoreOpsTry.branch r54)
                                                                                      match cf36 with
                                                                                      | core.ops.control_flow.ControlFlow.Continue val36 =>
                                                                                        let r55 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                                                            letI : ProverRwFull.ExternalFuns := ops
                                                                                            atomic_statement.decode_digest_canonical val36)
                                                                                        let r56 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                                            letI : ProverRwFull.ExternalFuns := ops
                                                                                            core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r55 ())
                                                                                        let cf37 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                            letI : ProverRwFull.ExternalFuns := ops
                                                                                            core.result.Result.Insts.CoreOpsTry.branch r56)
                                                                                        match cf37 with
                                                                                        | core.ops.control_flow.ControlFlow.Continue val37 =>
                                                                                          let s21 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                                              letI : ProverRwFull.ExternalFuns := ops
                                                                                              core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 624#usize, «end» := 656#usize })
                                                                                          let r57 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                                                              letI : ProverRwFull.ExternalFuns := ops
                                                                                              pool_v1.pair_terminal.exact 32#usize s21)
                                                                                          let cf38 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                              letI : ProverRwFull.ExternalFuns := ops
                                                                                              core.result.Result.Insts.CoreOpsTry.branch r57)
                                                                                          match cf38 with
                                                                                          | core.ops.control_flow.ControlFlow.Continue val38 =>
                                                                                            let r58 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                                                atomic_statement.decode_digest_canonical val38)
                                                                                            let r59 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                                                core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r58 ())
                                                                                            let cf39 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                                                core.result.Result.Insts.CoreOpsTry.branch r59)
                                                                                            match cf39 with
                                                                                            | core.ops.control_flow.ControlFlow.Continue val39 =>
                                                                                              let s22 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                                                  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 656#usize, «end» := 688#usize })
                                                                                              let r60 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                                                  pool_v1.pair_terminal.exact 32#usize s22)
                                                                                              let cf40 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                                                  core.result.Result.Insts.CoreOpsTry.branch r60)
                                                                                              match cf40 with
                                                                                              | core.ops.control_flow.ControlFlow.Continue val40 =>
                                                                                                let r61 ← invoke "atomic_statement.decode_digest_canonical" (fun ops =>
                                                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                                                    atomic_statement.decode_digest_canonical val40)
                                                                                                let r62 ← invoke "core.result.Result.map_err" (fun ops =>
                                                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                                                    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r61 ())
                                                                                                let cf41 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                                                    core.result.Result.Insts.CoreOpsTry.branch r62)
                                                                                                match cf41 with
                                                                                                | core.ops.control_flow.ControlFlow.Continue val41 =>
                                                                                                  let s23 ← invoke "core.slice.index.Slice.index" (fun ops =>
                                                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                                                      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 8#usize, «end» := 16#usize })
                                                                                                  let r63 ← invoke "pool_v1.pair_terminal.exact" (fun ops =>
                                                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                                                      pool_v1.pair_terminal.exact 8#usize s23)
                                                                                                  let cf42 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                                                      core.result.Result.Insts.CoreOpsTry.branch r63)
                                                                                                  match cf42 with
                                                                                                  | core.ops.control_flow.ControlFlow.Continue val42 =>
                                                                                                    let i6 ← invoke "lift" (fun ops =>
                                                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                                                        lift (core.num.U64.from_le_bytes val42))
                                                                                                    let r64 ← invoke "pool_v1.pair_terminal.validate_verified_afterstate" (fun ops =>
                                                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                                                        pool_v1.pair_terminal.validate_verified_afterstate { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) })
                                                                                                    let cf43 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                                                        core.result.Result.Insts.CoreOpsTry.branch r64)
                                                                                                    match cf43 with
                                                                                                    | core.ops.control_flow.ControlFlow.Continue _ =>
                                                                                                      pure (core.result.Result.Ok { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) })
                                                                                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                                      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                                                  | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                                                | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                                              | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                                            | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                                          | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                              letI : ProverRwFull.ExternalFuns := ops
                                                                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                                        | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                            letI : ProverRwFull.ExternalFuns := ops
                                                                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                                      | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                          letI : ProverRwFull.ExternalFuns := ops
                                                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                                  | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                                | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                              | core.ops.control_flow.ControlFlow.Break residual =>
                                                                                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                            | core.ops.control_flow.ControlFlow.Break residual =>
                                                                              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                          | core.ops.control_flow.ControlFlow.Break residual =>
                                                                            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                              letI : ProverRwFull.ExternalFuns := ops
                                                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                        | core.ops.control_flow.ControlFlow.Break residual =>
                                                                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                            letI : ProverRwFull.ExternalFuns := ops
                                                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                      | core.ops.control_flow.ControlFlow.Break residual =>
                                                                        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                          letI : ProverRwFull.ExternalFuns := ops
                                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                                                      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                        letI : ProverRwFull.ExternalFuns := ops
                                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                  | core.ops.control_flow.ControlFlow.Break residual =>
                                                                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                      letI : ProverRwFull.ExternalFuns := ops
                                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                                | core.ops.control_flow.ControlFlow.Break residual =>
                                                                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                    letI : ProverRwFull.ExternalFuns := ops
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                              | core.ops.control_flow.ControlFlow.Break residual =>
                                                                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                  letI : ProverRwFull.ExternalFuns := ops
                                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                            | core.ops.control_flow.ControlFlow.Break residual =>
                                                              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                                letI : ProverRwFull.ExternalFuns := ops
                                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                          | core.ops.control_flow.ControlFlow.Break residual =>
                                                            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                              letI : ProverRwFull.ExternalFuns := ops
                                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                        | core.ops.control_flow.ControlFlow.Break residual =>
                                                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                            letI : ProverRwFull.ExternalFuns := ops
                                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                      | core.ops.control_flow.ControlFlow.Break residual =>
                                                        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                          letI : ProverRwFull.ExternalFuns := ops
                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                                      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                        letI : ProverRwFull.ExternalFuns := ops
                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                  | core.ops.control_flow.ControlFlow.Break residual =>
                                                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                      letI : ProverRwFull.ExternalFuns := ops
                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                                | core.ops.control_flow.ControlFlow.Break residual =>
                                                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                    letI : ProverRwFull.ExternalFuns := ops
                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                              | core.ops.control_flow.ControlFlow.Break residual =>
                                                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                  letI : ProverRwFull.ExternalFuns := ops
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                            | core.ops.control_flow.ControlFlow.Break residual =>
                                              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                                letI : ProverRwFull.ExternalFuns := ops
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                          | core.ops.control_flow.ControlFlow.Break residual =>
                                            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                              letI : ProverRwFull.ExternalFuns := ops
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                        | core.ops.control_flow.ControlFlow.Break residual =>
                                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                            letI : ProverRwFull.ExternalFuns := ops
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                      | core.ops.control_flow.ControlFlow.Break residual =>
                                        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                          letI : ProverRwFull.ExternalFuns := ops
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                    | core.ops.control_flow.ControlFlow.Break residual =>
                                      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                        letI : ProverRwFull.ExternalFuns := ops
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                  | core.ops.control_flow.ControlFlow.Break residual =>
                                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                      letI : ProverRwFull.ExternalFuns := ops
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                                | core.ops.control_flow.ControlFlow.Break residual =>
                                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                    letI : ProverRwFull.ExternalFuns := ops
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                              | core.ops.control_flow.ControlFlow.Break residual =>
                                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                  letI : ProverRwFull.ExternalFuns := ops
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                            | core.ops.control_flow.ControlFlow.Break residual =>
                              invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                                letI : ProverRwFull.ExternalFuns := ops
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                              letI : ProverRwFull.ExternalFuns := ops
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                            letI : ProverRwFull.ExternalFuns := ops
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                          letI : ProverRwFull.ExternalFuns := ops
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                        letI : ProverRwFull.ExternalFuns := ops
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                      letI : ProverRwFull.ExternalFuns := ops
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                    letI : ProverRwFull.ExternalFuns := ops
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)
              | core.ops.control_flow.ControlFlow.Break residual =>
                invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
                  letI : ProverRwFull.ExternalFuns := ops
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (bytes : Slice Std.U8) :
  erase ops (program bytes) =
    pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes := by
  unfold program pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
  try dsimp only
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
                              · intro s2
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
                                  · intro cf
                                    try dsimp only
                                    cases cf with
                                    | Continue val =>
                                      try dsimp only
                                      rw [erase_bind]
                                      apply PV_W_RecursiveLaws.bind_congr
                                      ·
                                        exact erase_invoke ops _ _
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
                                          · intro cf1
                                            try dsimp only
                                            cases cf1 with
                                            | Continue val1 =>
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
                                                · intro r3
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
                                                          · intro cf3
                                                            try dsimp only
                                                            cases cf3 with
                                                            | Continue val3 =>
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
                                                                · intro r6
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
                                                                          · intro cf5
                                                                            try dsimp only
                                                                            cases cf5 with
                                                                            | Continue val5 =>
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
                                                                                · intro r9
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
                                                                                          · intro cf7
                                                                                            try dsimp only
                                                                                            cases cf7 with
                                                                                            | Continue val7 =>
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
                                                                                                · intro r12
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
                                                                                                          · intro cf9
                                                                                                            try dsimp only
                                                                                                            cases cf9 with
                                                                                                            | Continue val9 =>
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
                                                                                                                · intro r15
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
                                                                                                                          · intro cf11
                                                                                                                            try dsimp only
                                                                                                                            cases cf11 with
                                                                                                                            | Continue val11 =>
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
                                                                                                                                · intro r18
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
                                                                                                                                          · intro cf13
                                                                                                                                            try dsimp only
                                                                                                                                            cases cf13 with
                                                                                                                                            | Continue val13 =>
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
                                                                                                                                                · intro r21
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
                                                                                                                                                          · intro cf15
                                                                                                                                                            try dsimp only
                                                                                                                                                            cases cf15 with
                                                                                                                                                            | Continue val15 =>
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
                                                                                                                                                                · intro r24
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
                                                                                                                                                                          · intro cf17
                                                                                                                                                                            try dsimp only
                                                                                                                                                                            cases cf17 with
                                                                                                                                                                            | Continue val17 =>
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
                                                                                                                                                                                · intro r27
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
                                                                                                                                                                                          · intro cf19
                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                            cases cf19 with
                                                                                                                                                                                            | Continue val19 =>
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
                                                                                                                                                                                                · intro r30
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
                                                                                                                                                                                                          · intro cf21
                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                            cases cf21 with
                                                                                                                                                                                                            | Continue val21 =>
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
                                                                                                                                                                                                                · intro r33
                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                  · intro cf22
                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                    cases cf22 with
                                                                                                                                                                                                                    | Continue val22 =>
                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                        exact erase_invoke ops _ _
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
                                                                                                                                                                                                                          · intro cf23
                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                            cases cf23 with
                                                                                                                                                                                                                            | Continue val23 =>
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
                                                                                                                                                                                                                                · intro r36
                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                  · intro cf24
                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                    cases cf24 with
                                                                                                                                                                                                                                    | Continue val24 =>
                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                        exact erase_invoke ops _ _
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
                                                                                                                                                                                                                                          · intro cf25
                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                            cases cf25 with
                                                                                                                                                                                                                                            | Continue val25 =>
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
                                                                                                                                                                                                                                                · intro r39
                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                  · intro cf26
                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                    cases cf26 with
                                                                                                                                                                                                                                                    | Continue val26 =>
                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
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
                                                                                                                                                                                                                                                          · intro cf27
                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                            cases cf27 with
                                                                                                                                                                                                                                                            | Continue val27 =>
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
                                                                                                                                                                                                                                                                · intro r42
                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                  · intro cf28
                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                    cases cf28 with
                                                                                                                                                                                                                                                                    | Continue val28 =>
                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
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
                                                                                                                                                                                                                                                                          · intro cf29
                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                            cases cf29 with
                                                                                                                                                                                                                                                                            | Continue val29 =>
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
                                                                                                                                                                                                                                                                                · intro r45
                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                  · intro cf30
                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                    cases cf30 with
                                                                                                                                                                                                                                                                                    | Continue val30 =>
                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
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
                                                                                                                                                                                                                                                                                          · intro cf31
                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                            cases cf31 with
                                                                                                                                                                                                                                                                                            | Continue val31 =>
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
                                                                                                                                                                                                                                                                                                · intro r48
                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                  · intro cf32
                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                    cases cf32 with
                                                                                                                                                                                                                                                                                                    | Continue val32 =>
                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
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
                                                                                                                                                                                                                                                                                                          · intro cf33
                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                            cases cf33 with
                                                                                                                                                                                                                                                                                                            | Continue val33 =>
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
                                                                                                                                                                                                                                                                                                                · intro r51
                                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                  · intro cf34
                                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                                    cases cf34 with
                                                                                                                                                                                                                                                                                                                    | Continue val34 =>
                                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
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
                                                                                                                                                                                                                                                                                                                          · intro cf35
                                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                                            cases cf35 with
                                                                                                                                                                                                                                                                                                                            | Continue val35 =>
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
                                                                                                                                                                                                                                                                                                                                · intro r54
                                                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                  · intro cf36
                                                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                                                    cases cf36 with
                                                                                                                                                                                                                                                                                                                                    | Continue val36 =>
                                                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
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
                                                                                                                                                                                                                                                                                                                                          · intro cf37
                                                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                                                            cases cf37 with
                                                                                                                                                                                                                                                                                                                                            | Continue val37 =>
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
                                                                                                                                                                                                                                                                                                                                                · intro r57
                                                                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                  · intro cf38
                                                                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                                                                    cases cf38 with
                                                                                                                                                                                                                                                                                                                                                    | Continue val38 =>
                                                                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
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
                                                                                                                                                                                                                                                                                                                                                          · intro cf39
                                                                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                                                                            cases cf39 with
                                                                                                                                                                                                                                                                                                                                                            | Continue val39 =>
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
                                                                                                                                                                                                                                                                                                                                                                · intro r60
                                                                                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                  · intro cf40
                                                                                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                                                                                    cases cf40 with
                                                                                                                                                                                                                                                                                                                                                                    | Continue val40 =>
                                                                                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
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
                                                                                                                                                                                                                                                                                                                                                                          · intro cf41
                                                                                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                                                                                            cases cf41 with
                                                                                                                                                                                                                                                                                                                                                                            | Continue val41 =>
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
                                                                                                                                                                                                                                                                                                                                                                                · intro r63
                                                                                                                                                                                                                                                                                                                                                                                  try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                  rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                                  apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                                                    exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                                  · intro cf42
                                                                                                                                                                                                                                                                                                                                                                                    try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                    cases cf42 with
                                                                                                                                                                                                                                                                                                                                                                                    | Continue val42 =>
                                                                                                                                                                                                                                                                                                                                                                                      try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                      rw [erase_bind]
                                                                                                                                                                                                                                                                                                                                                                                      apply PV_W_RecursiveLaws.bind_congr
                                                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                                                        exact erase_invoke ops _ _
                                                                                                                                                                                                                                                                                                                                                                                      · intro i6
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
                                                                                                                                                                                                                                                                                                                                                                                          · intro cf43
                                                                                                                                                                                                                                                                                                                                                                                            try dsimp only
                                                                                                                                                                                                                                                                                                                                                                                            cases cf43 with
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
end R1Z.PV_RJDec_Parser15
