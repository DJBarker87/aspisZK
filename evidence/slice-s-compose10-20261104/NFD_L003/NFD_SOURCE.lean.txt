import JHd_RequestNative
import NED_RequestReadWindows
set_option autoImplicit false
noncomputable section
namespace NFD_RequestOracle
open Aeneas Aeneas.Std Result AspisR20Request
def run
  (transfer : Slice U8 → Result (core.result.Result pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 pool_v1.payment_relation.PoolV1PaymentStatementFormatError))
  (withdrawal : Slice U8 → Result (core.result.Result pool_v1.payment_relation.PoolV1WithdrawalPublicV1 pool_v1.payment_relation.PoolV1PaymentStatementFormatError))
  (bytes : Array Std.U8 320#usize) :
  Result (core.result.Result
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  let s ← lift (Array.to_slice bytes)
  let i := Slice.len s
  let i1 ←
    pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  if i != i1
  then
    ok (core.result.Result.Err
      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength)
  else
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) bytes
        { «end» := 4#usize }
    let b ←
      Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 s1
        pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC
    if b
    then
      ok (core.result.Result.Err
        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongMagic)
    else
      let i2 ← Array.index_usize bytes 4#usize
      if i2 !=
        pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
      then
        ok (core.result.Result.Err
          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongVersion)
      else
        let i3 ← Array.index_usize bytes 5#usize
        let r ← pool_v1.pair_forest_terminal.transition_kind i3
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let i4 ← Array.index_usize bytes 6#usize
          if i4 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
          then
            ok (core.result.Result.Err
              pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongDigestEncoding)
          else
            let i5 ← Array.index_usize bytes 7#usize
            if i5 != 0#u8
            then
              ok (core.result.Result.Err
                pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
            else
              match val with
              | pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
                =>
                let s2 ←
                  core.array.Array.index (core.ops.index.IndexSlice
                    (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8))
                    bytes
                    {
                      start :=
                        pool_v1.pair_forest_terminal.REQUEST_PAYMENT_OFFSET
                    }
                let r1 ←
                  transfer
                    s2
                let r2 ←
                  core.result.Result.map_err
                    pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
                    r1 ()
                let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val1 =>
                  let s3 ←
                    core.array.Array.index (core.ops.index.IndexSlice
                      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                      bytes
                      {
                        start :=
                          pool_v1.pair_forest_terminal.REQUEST_PROFILE_OFFSET,
                        «end» :=
                          pool_v1.pair_forest_terminal.REQUEST_RELEASE_OFFSET
                      }
                  let r3 ←
                    core.array.TryFromArrayCopySlice.try_from 32#usize
                      core.marker.CopyU8 s3
                  let r4 ←
                    core.result.Result.map_err
                      pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                      r3 ()
                  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
                  match cf2 with
                  | core.ops.control_flow.ControlFlow.Continue val2 =>
                    let s4 ←
                      core.array.Array.index (core.ops.index.IndexSlice
                        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                        bytes
                        {
                          start :=
                            pool_v1.pair_forest_terminal.REQUEST_RELEASE_OFFSET,
                          «end» :=
                            pool_v1.pair_forest_terminal.REQUEST_POOL_PROGRAM_OFFSET
                        }
                    let r5 ←
                      core.array.TryFromArrayCopySlice.try_from 32#usize
                        core.marker.CopyU8 s4
                    let r6 ←
                      core.result.Result.map_err
                        pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                        r5 ()
                    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf3 with
                    | core.ops.control_flow.ControlFlow.Continue val3 =>
                      let s5 ←
                        core.array.Array.index (core.ops.index.IndexSlice
                          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                          bytes
                          {
                            start :=
                              pool_v1.pair_forest_terminal.REQUEST_POOL_PROGRAM_OFFSET,
                            «end» :=
                              pool_v1.pair_forest_terminal.REQUEST_PAYMENT_OFFSET
                          }
                      let r7 ←
                        core.array.TryFromArrayCopySlice.try_from 32#usize
                          core.marker.CopyU8 s5
                      let r8 ←
                        core.result.Result.map_err
                          pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                          r7 ()
                      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r8
                      match cf4 with
                      | core.ops.control_flow.ControlFlow.Continue val4 =>
                        let a := Array.repeat 32#usize 0#u8
                        let b1 ←
                          core.array.equality.PartialEqArray.eq
                            core.cmp.PartialEqU8 val2 a
                        if b1
                        then
                          ok (core.result.Result.Err
                            pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                        else
                          let a1 := Array.repeat 32#usize 0#u8
                          let b2 ←
                            core.array.equality.PartialEqArray.eq
                              core.cmp.PartialEqU8 val3 a1
                          if b2
                          then
                            ok (core.result.Result.Err
                              pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                          else
                            let a2 := Array.repeat 32#usize 0#u8
                            let b3 ←
                              core.array.equality.PartialEqArray.eq
                                core.cmp.PartialEqU8 val4 a2
                            if b3
                            then
                              ok (core.result.Result.Err
                                pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                            else
                              ok (core.result.Result.Ok
                                {
                                  verifier_profile := val2,
                                  verifier_release := val3,
                                  pool_program := val4,
                                  «public» :=
                                    (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1.PrivateTransfer
                                      val1)
                                })
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                          (core.convert.FromSame
                          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                          residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                        (core.convert.FromSame
                        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                        residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                      (core.convert.FromSame
                      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                    (core.convert.FromSame
                    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                    residual
              | pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal =>
                let s2 ←
                  core.array.Array.index (core.ops.index.IndexSlice
                    (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8))
                    bytes
                    {
                      start :=
                        pool_v1.pair_forest_terminal.REQUEST_PAYMENT_OFFSET
                    }
                let r1 ←
                  withdrawal
                    s2
                let r2 ←
                  core.result.Result.map_err
                    pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
                    r1 ()
                let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val1 =>
                  let s3 ←
                    core.array.Array.index (core.ops.index.IndexSlice
                      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                      bytes
                      {
                        start :=
                          pool_v1.pair_forest_terminal.REQUEST_PROFILE_OFFSET,
                        «end» :=
                          pool_v1.pair_forest_terminal.REQUEST_RELEASE_OFFSET
                      }
                  let r3 ←
                    core.array.TryFromArrayCopySlice.try_from 32#usize
                      core.marker.CopyU8 s3
                  let r4 ←
                    core.result.Result.map_err
                      pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                      r3 ()
                  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
                  match cf2 with
                  | core.ops.control_flow.ControlFlow.Continue val2 =>
                    let s4 ←
                      core.array.Array.index (core.ops.index.IndexSlice
                        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                        bytes
                        {
                          start :=
                            pool_v1.pair_forest_terminal.REQUEST_RELEASE_OFFSET,
                          «end» :=
                            pool_v1.pair_forest_terminal.REQUEST_POOL_PROGRAM_OFFSET
                        }
                    let r5 ←
                      core.array.TryFromArrayCopySlice.try_from 32#usize
                        core.marker.CopyU8 s4
                    let r6 ←
                      core.result.Result.map_err
                        pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                        r5 ()
                    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf3 with
                    | core.ops.control_flow.ControlFlow.Continue val3 =>
                      let s5 ←
                        core.array.Array.index (core.ops.index.IndexSlice
                          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                          bytes
                          {
                            start :=
                              pool_v1.pair_forest_terminal.REQUEST_POOL_PROGRAM_OFFSET,
                            «end» :=
                              pool_v1.pair_forest_terminal.REQUEST_PAYMENT_OFFSET
                          }
                      let r7 ←
                        core.array.TryFromArrayCopySlice.try_from 32#usize
                          core.marker.CopyU8 s5
                      let r8 ←
                        core.result.Result.map_err
                          pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                          r7 ()
                      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r8
                      match cf4 with
                      | core.ops.control_flow.ControlFlow.Continue val4 =>
                        let a := Array.repeat 32#usize 0#u8
                        let b1 ←
                          core.array.equality.PartialEqArray.eq
                            core.cmp.PartialEqU8 val2 a
                        if b1
                        then
                          ok (core.result.Result.Err
                            pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                        else
                          let a1 := Array.repeat 32#usize 0#u8
                          let b2 ←
                            core.array.equality.PartialEqArray.eq
                              core.cmp.PartialEqU8 val3 a1
                          if b2
                          then
                            ok (core.result.Result.Err
                              pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                          else
                            let a2 := Array.repeat 32#usize 0#u8
                            let b3 ←
                              core.array.equality.PartialEqArray.eq
                                core.cmp.PartialEqU8 val4 a2
                            if b3
                            then
                              ok (core.result.Result.Err
                                pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                            else
                              ok (core.result.Result.Ok
                                {
                                  verifier_profile := val2,
                                  verifier_release := val3,
                                  pool_program := val4,
                                  «public» :=
                                    (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1.Withdrawal
                                      val1)
                                })
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                          (core.convert.FromSame
                          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                          residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                        (core.convert.FromSame
                        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                        residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                      (core.convert.FromSame
                      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                    (core.convert.FromSame
                    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                    residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
            (core.convert.FromSame
            pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
            residual

/-- MODEL continuation part of ruling(y). The native certificate must separately
establish the exact same320-byte input and216-byte payment window. -/
theorem array_result_state_effects {State : Type} (bytes : Array U8 320#usize) (state : State) :
    (run pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 bytes,state,([] : List Unit)) =
    (pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1 bytes,state,[]) := by rfl

/-- The installed wrapper keeps every error constructor and the same parsed
request; no accepted fixture is assumed. -/
def runSlice (bytes : Slice U8) : Result (core.result.Result AspisR1.JHd_RequestNative.Request AspisR1.JHd_RequestNative.FormatError) := do
  let array ← core.array.TryFromSharedArraySlice.try_from 320#usize bytes
  match array with
  | .Err _ => ok (.Err AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength)
  | .Ok array =>
    let result ← run pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 array
    match result with
    | .Err error => ok (.Err (AspisR1.JHd_RequestCarrier.mapPoolV1PairForestTerminalFormatErrorV1 error))
    | .Ok request => ok (.Ok (AspisR1.JHd_RequestCarrier.request request))

theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (runSlice bytes,state,([] : List Unit)) =
    (AspisR1.JHd_RequestNative.decode bytes,state,[]) := by rfl

#print axioms array_result_state_effects
#print axioms result_state_effects
end NFD_RequestOracle
