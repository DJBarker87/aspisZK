import Lean
import NGK_NFO_RawDecode

set_option autoImplicit false
noncomputable section
namespace NGK_NFO_DecodeOracle
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
def run
    (digest : Array U8 32#usize → Result (core.result.Result (Array U32 8#usize) atomic_statement.AtomicStatementError))
    (afterstate : Slice U8 → Result (core.result.Result pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1))
    (validate : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1 → Result (core.result.Result Unit pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))
  (bytes : Slice Std.U8) :
  Result (core.result.Result
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  let i := Slice.len bytes
  let i1 :=
    792#usize
  if i != i1
  then
    ok (core.result.Result.Err
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength)
  else
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes
        { «end» := 4#usize }
    let a :=
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s (Array.to_slice a)
    if b
    then
      ok (core.result.Result.Err
        AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongMagic)
    else
      let i2 ← Slice.index_usize bytes 4#usize
      let i3 :=
        AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
      if i2 != i3
      then
        ok (core.result.Result.Err
          AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongVersion)
      else
        let i4 ← Slice.index_usize bytes 5#usize
        let r ←
          AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.transition_kind i4
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let i5 ← Slice.index_usize bytes 6#usize
          let i6 :=
            AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
          if i5 != i6
          then
            ok (core.result.Result.Err
              AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongDigestEncoding)
          else
            let i7 :=
              AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET
            let i8 :=
              AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                { start := i7, «end» := i8 }
            let r1 ←
              core.array.TryFromArrayCopySlice.try_from 32#usize
                core.marker.CopyU8 s1
            let r2 ←
              core.result.Result.map_err
                NGK_NFO_RawDecode.decode.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                r1 ()
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue val1 =>
              let i9 :=
                AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                  { start := i8, «end» := i9 }
              let r3 ←
                core.array.TryFromArrayCopySlice.try_from 32#usize
                  core.marker.CopyU8 s2
              let r4 ←
                core.result.Result.map_err
                  NGK_NFO_RawDecode.decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                  r3 ()
              let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf2 with
              | core.ops.control_flow.ControlFlow.Continue val2 =>
                let i10 ← Slice.index_usize bytes 7#usize
                let i11 :=
                  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET
                let s3 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                    { start := i9, «end» := i11 }
                let r5 ←
                  core.array.TryFromSharedArraySlice.try_from 32#usize s3
                let r6 ←
                  core.result.Result.map_err
                    NGK_NFO_RawDecode.decode.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                    r5 ()
                let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf3 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let r7 ←
                    digest
                      val3
                  let r8 ←
                    core.result.Result.map_err
                      NGK_NFO_RawDecode.decode.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1
                      r7 ()
                  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf4 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let s4 ←
                      core.slice.index.Slice.index
                        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                        bytes { start := i11 }
                    let r9 ←
                      afterstate
                        s4
                    let r10 ←
                      core.result.Result.map_err
                        NGK_NFO_RawDecode.decode.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1
                        r9 ()
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r10
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let r11 ←
                        validate
                          {
                            transition_kind := val,
                            master_account := val1,
                            selected_lane_account := val2,
                            output_lane := i10,
                            nullifier := val4,
                            verified_afterstate := val5
                          }
                      let cf6 ←
                        core.result.Result.Insts.CoreOpsTry.branch r11
                      match cf6 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        ok (core.result.Result.Ok
                          {
                            transition_kind := val,
                            master_account := val1,
                            selected_lane_account := val2,
                            output_lane := i10,
                            nullifier := val4,
                            verified_afterstate := val5
                          })
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
                          (core.convert.FromSame
                          AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                          residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
                        (core.convert.FromSame
                        AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                        residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
                      (core.convert.FromSame
                      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
                    (core.convert.FromSame
                    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
                  (core.convert.FromSame
                  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
                (core.convert.FromSame
                AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
            (core.convert.FromSame
            AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
            residual
theorem substitution (bytes : Slice U8) :
    run atomic_statement.decode_digest_canonical
      pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
      pool_v1.pair_forest_terminal.validate_result bytes = NGK_NFO_RawDecode.decode bytes := rfl
#print axioms substitution
end NGK_NFO_DecodeOracle

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
