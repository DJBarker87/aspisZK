import Lean
import NGK_NFO_RawDecode
import NGK_NFO_DecodeOracle

set_option autoImplicit false
noncomputable section
namespace NGK_NFR_ExtractedDecode
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
def resultBytes : Result Usize := ok 792#usize
def resultMagic := ok pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC
def resultVersion := ok pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
def digestVersion := ok pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
def masterOffset := ok pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET
def selectedOffset := ok pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET
def nullifierOffset := ok pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET
def afterstateOffset := ok pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET
/-- Interpretation of E001's external slice/array comparison on canonical carriers. -/
def sliceArrayNe {n : Usize} (s : Slice U8) (a : Array U8 n) : Result Bool :=
  core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s (Array.to_slice a)
theorem sliceArrayNe_eq {n : Usize} (s : Slice U8) (a : Array U8 n) :
    sliceArrayNe s a =
      core.cmp.PartialEq.ne.trait_default
        (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s (Array.to_slice a) := rfl
#print axioms sliceArrayNe_eq
def decode.closure_4
  :=
Unit

def decode.closure_3
  :=
Unit

def decode.closure_2
  :=
Unit

def decode.closure_1
  :=
Unit

def decode.closure
  :=
Unit

def
  decode.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
  (c :
  decode.closure_4)
  (tupled_args :
  AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
  Result
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := do
  ok
    (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Afterstate
    tupled_args)

def
  decode.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1
  : core.ops.function.FnOnce
  decode.closure_4
  AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := {
  call_once :=
    decode.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once
}

def
  decode.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1.call_once
  (c :
  decode.closure_3)
  (tupled_args : AspisR1TerminalDecoder.atomic_statement.AtomicStatementError) :
  Result
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := do
  ok
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonCanonicalDigest

def
  decode.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1
  : core.ops.function.FnOnce
  decode.closure_3
  AspisR1TerminalDecoder.atomic_statement.AtomicStatementError
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := {
  call_once :=
    decode.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1.call_once
}

def
  decode.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once
  (c :
  decode.closure_2)
  (tupled_args : core.array.TryFromSliceError) :
  Result
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := do
  ok
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength

def
  decode.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
  : core.ops.function.FnOnce
  decode.closure_2
  core.array.TryFromSliceError
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := {
  call_once :=
    decode.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once
}

def
  decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once
  (c :
  decode.closure_1)
  (tupled_args : core.array.TryFromSliceError) :
  Result
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := do
  ok
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength

def
  decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
  : core.ops.function.FnOnce
  decode.closure_1
  core.array.TryFromSliceError
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := {
  call_once :=
    decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once
}

def
  decode.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once
  (c :
  decode.closure)
  (tupled_args : core.array.TryFromSliceError) :
  Result
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := do
  ok
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength

def
  decode.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
  : core.ops.function.FnOnce
  decode.closure
  core.array.TryFromSliceError
  AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  := {
  call_once :=
    decode.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once
}

def
  decode
  (bytes : Slice Std.U8) :
  Result (core.result.Result
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  let i := Slice.len bytes
  let i1 ←
    resultBytes
  if i != i1
  then
    ok (core.result.Result.Err
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength)
  else
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes
        { «end» := 4#usize }
    let a ←
      resultMagic
    let b ← sliceArrayNe s a
    if b
    then
      ok (core.result.Result.Err
        AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongMagic)
    else
      let i2 ← Slice.index_usize bytes 4#usize
      let i3 ←
        resultVersion
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
          let i6 ←
            digestVersion
          if i5 != i6
          then
            ok (core.result.Result.Err
              AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongDigestEncoding)
          else
            let i7 ←
              masterOffset
            let i8 ←
              selectedOffset
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                { start := i7, «end» := i8 }
            let r1 ←
              core.array.TryFromArrayCopySlice.try_from 32#usize
                core.marker.CopyU8 s1
            let r2 ←
              core.result.Result.map_err
                decode.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                r1 ()
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue val1 =>
              let i9 ←
                nullifierOffset
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                  { start := i8, «end» := i9 }
              let r3 ←
                core.array.TryFromArrayCopySlice.try_from 32#usize
                  core.marker.CopyU8 s2
              let r4 ←
                core.result.Result.map_err
                  decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                  r3 ()
              let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf2 with
              | core.ops.control_flow.ControlFlow.Continue val2 =>
                let i10 ← Slice.index_usize bytes 7#usize
                let i11 ←
                  afterstateOffset
                let s3 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                    { start := i9, «end» := i11 }
                let r5 ←
                  core.array.TryFromSharedArraySlice.try_from 32#usize s3
                let r6 ←
                  core.result.Result.map_err
                    decode.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                    r5 ()
                let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf3 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let r7 ←
                    AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical
                      val3
                  let r8 ←
                    core.result.Result.map_err
                      decode.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairForestTerminalFormatErrorV1
                      r7 ()
                  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf4 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let s4 ←
                      core.slice.index.Slice.index
                        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                        bytes { start := i11 }
                    let r9 ←
                      AspisR1TerminalDecoder.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
                        s4
                    let r10 ←
                      core.result.Result.map_err
                        decode.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairForestTerminalFormatErrorV1
                        r9 ()
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r10
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let r11 ←
                        AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_result
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
theorem probe (bytes : Slice U8) : decode bytes = NGK_NFO_RawDecode.decode bytes := by
  rfl
#print axioms probe
theorem oracle (bytes : Slice U8) :
    NGK_NFO_DecodeOracle.run atomic_statement.decode_digest_canonical
      pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
      pool_v1.pair_forest_terminal.validate_result bytes = decode bytes :=
  (NGK_NFO_DecodeOracle.substitution bytes).trans (probe bytes).symm
#print axioms oracle
end NGK_NFR_ExtractedDecode

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
