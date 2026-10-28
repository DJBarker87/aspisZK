import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_Parser03
import R1Z.PV_RJDec_Parser14
import R1Z.PV_RJDec_Parser05
import R1Z.PV_RJDec_SnapshotChunk20
import R1Z.PV_RJDec_SnapshotChunk16
import R1Z.PV_RJDec_SnapshotChunk12
import R1Z.PV_RJDec_SnapshotChunk08
import R1Z.PV_RJDec_SnapshotChunk04
import R1Z.PV_RJDec_SnapshotChunk00
import R1Z.PV_RJDec_AfterChunk41
import R1Z.PV_RJDec_AfterChunk33
import R1Z.PV_RJDec_AfterChunk25
import R1Z.PV_RJDec_AfterChunk17
import R1Z.PV_RJDec_AfterChunk9
import R1Z.PV_RunJoin_KernelRefl29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_ParserR15
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
open pool_v1.pair_tree_profile pool_v1.pair_terminal
variable [ProverRwFull.ExternalTypes]

def reference (bytes : Slice Std.U8) : Result (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
  let i := Slice.len bytes
  let i1 ← pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
  if i != i1
  then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongLength)
  else
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 4#usize }
    let s1 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC { start := 0#usize, «end» := 4#usize }
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1
    if b
    then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongMagic)
    else
      let i2 ← Slice.index_usize bytes 4#usize
      if i2 != pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
      then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongVersion)
      else
        let i3 ← Slice.index_usize bytes 5#usize
        if i3 != pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
        then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongPairFormat)
        else
          let i4 ← Slice.index_usize bytes 6#usize
          if i4 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
          then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongDigestEncoding)
          else
            let i5 ← Slice.index_usize bytes 7#usize
            if i5 != 1#u8
            then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongSuccessCode)
            else
              let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize }
              let r ← pool_v1.pair_terminal.exact 32#usize s2
              let cf ← core.result.Result.Insts.CoreOpsTry.branch r
              match cf with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r1 ← atomic_statement.decode_digest_canonical val
                let r2 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r1 ()
                let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val1 =>
                  let s3 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }
                  let r3 ← pool_v1.pair_terminal.exact 32#usize s3
                  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
                  match cf2 with
                  | core.ops.control_flow.ControlFlow.Continue val2 =>
                    let r4 ← atomic_statement.decode_digest_canonical val2
                    let r5 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r4 ()
                    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r5
                    match cf3 with
                    | core.ops.control_flow.ControlFlow.Continue val3 =>
                      let s4 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }
                      let r6 ← pool_v1.pair_terminal.exact 32#usize s4
                      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r6
                      match cf4 with
                      | core.ops.control_flow.ControlFlow.Continue val4 =>
                        let r7 ← atomic_statement.decode_digest_canonical val4
                        let r8 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r7 ()
                        let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r8
                        match cf5 with
                        | core.ops.control_flow.ControlFlow.Continue val5 =>
                          let s5 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 144#usize }
                          let r9 ← pool_v1.pair_terminal.exact 32#usize s5
                          let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r9
                          match cf6 with
                          | core.ops.control_flow.ControlFlow.Continue val6 =>
                            let r10 ← atomic_statement.decode_digest_canonical val6
                            let r11 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r10 ()
                            let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r11
                            match cf7 with
                            | core.ops.control_flow.ControlFlow.Continue val7 =>
                              let s6 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 144#usize, «end» := 176#usize }
                              let r12 ← pool_v1.pair_terminal.exact 32#usize s6
                              let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r12
                              match cf8 with
                              | core.ops.control_flow.ControlFlow.Continue val8 =>
                                let r13 ← atomic_statement.decode_digest_canonical val8
                                let r14 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r13 ()
                                let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r14
                                match cf9 with
                                | core.ops.control_flow.ControlFlow.Continue val9 =>
                                  R1Z.PV_RJDec_AfterChunk9.reference bytes val1 val3 val5 val7 val9
                                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

def program (bytes : Slice Std.U8) : P (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) := do
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
                let r1 ← R1Z.PV_RJDec_Parser03.program val
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
                    let r4 ← R1Z.PV_RJDec_Parser03.program val2
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
                        let r7 ← R1Z.PV_RJDec_Parser03.program val4
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
                            let r10 ← R1Z.PV_RJDec_Parser03.program val6
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
                                let r13 ← R1Z.PV_RJDec_Parser03.program val8
                                let r14 ← invoke "core.result.Result.map_err" (fun ops =>
                                    letI : ProverRwFull.ExternalFuns := ops
                                    core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r13 ())
                                let cf9 ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
                                    letI : ProverRwFull.ExternalFuns := ops
                                    core.result.Result.Insts.CoreOpsTry.branch r14)
                                match cf9 with
                                | core.ops.control_flow.ControlFlow.Continue val9 =>
                                  R1Z.PV_RJDec_AfterChunk9.program bytes val1 val3 val5 val7 val9
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

theorem source_chunk (ops : ProverRwFull.ExternalFuns) (bytes : Slice Std.U8) :
  erase ops (program bytes) = R1Z.PV_RJDec_ParserR15.reference bytes := by
  unfold program R1Z.PV_RJDec_ParserR15.reference
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
                                        exact R1Z.PV_RJDec_Parser03.source ops val
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
                                                        exact R1Z.PV_RJDec_Parser03.source ops val2
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
                                                                        exact R1Z.PV_RJDec_Parser03.source ops val4
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
                                                                                        exact R1Z.PV_RJDec_Parser03.source ops val6
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
                                                                                                        exact R1Z.PV_RJDec_Parser03.source ops val8
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
                                                                                                              exact R1Z.PV_RJDec_AfterChunk9.source ops bytes val1 val3 val5 val7 val9
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

theorem reference_source (bytes : Slice Std.U8) : reference bytes = pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes := by
  pv_kernel_refl

theorem source (ops : ProverRwFull.ExternalFuns) (bytes : Slice Std.U8) :
  erase ops (program bytes) = pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes :=
  (source_chunk ops bytes).trans (reference_source bytes)

#print axioms source
#print axioms source_chunk
#print axioms reference_source
end R1Z.PV_RJDec_ParserR15
