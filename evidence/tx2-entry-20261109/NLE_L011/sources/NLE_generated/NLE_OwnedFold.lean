import NLE_OwnedState
set_option autoImplicit false
noncomputable section
namespace NLE_Owned
open Aeneas Aeneas.Std Result AdapterRw
def G (ops : Ops) (initial : State)
  :
  Run (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let program_id := initial.frame.program
  let accounts := initial.frame.accounts
  let data := initial.frame.data
  let current_slot := initial.frame.slot
  let i := Slice.len accounts
  if i != 7#usize
  then
    pure (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let o ←
      core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice
        Std.U8) data { «end» := 4#usize }
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops)
        Std.U8))
        aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC
        ()
    let b ←
      core.cmp.PartialEq.ne.trait_default
        ((core.option.Option.Insts.CoreCmpPartialEqOption ops)
        (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice
        core.cmp.PartialEqU8))) o (some s)
    if b
    then
      pure (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let r ←
        NJU_Log.record (.validate initial)
          ((r1_pool_adapter.owned.validate_asq8 ops) program_id accounts data current_slot)
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let s1 := {initial with validated := some val}
        let oa ← Slice.index_usize accounts 0#usize
        let r1 ← NJU_Log.record (.proof s1 oa) ((r1_pool_adapter.owned.OwnedAccount.data ops) oa)
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let s2 := {s1 with proofBytes := some val1}
          let oa1 ← Slice.index_usize accounts 6#usize
          let r2 ← NJU_Log.record (.checkpoint s2 oa1) ((r1_pool_adapter.owned.OwnedAccount.data ops) oa1)
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s3 := {s2 with checkpoint := some val2}
            let proof_start ←
              (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
            let o1 ← lift (Usize.checked_add proof_start val.proof_length)
            let r3 ←
              core.option.Option.ok_or o1
                solana_program_error.ProgramError.InvalidAccountData
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let s4 := {s3 with proofEnd := some val3}
              let i1 := Slice.len val1
              if i1 != val3
              then
                pure (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData)
              else
                let r4 ←
                  NJU_Log.record (.encode s4 val.statement) (ops.op22 val.statement)
                let r5 ←
                  core.result.Result.map_err
                    r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                    r4 ()
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let s5 := {s4 with publicBytes := some val4}
                  let s1 ← lift (Array.to_slice val4)
                  let i2 := Slice.len s1
                  let i3 ←
                    (aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops)
                  if i2 != i3
                  then
                    pure (core.result.Result.Err
                      solana_program_error.ProgramError.InvalidInstructionData)
                  else
                    let s2 ← lift (Array.to_slice val4)
                    let s3 ←
                      core.slice.index.Slice.index
                        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                        val1 { start := proof_start, «end» := val3 }
                    let o2 ← (observer ops)
                    let r6 ←
                      NJU_Log.record (.tx2 s5 s2 s3 val2)
                        (ops.op11 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) s2 s3 val2 () o2)
                    let r7 ←
                      core.result.Result.map_err (BuiltinFnOnce
                        aspis_r1_cost_probe.verifier.Error
                        solana_program_error.ProgramError) r6 (ops.op44)
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue _ =>
                      NJU_Log.record (.emit s5 val.statement) (ops.op53 val.statement)
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Unit (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame
                    solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame solana_program_error.ProgramError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame solana_program_error.ProgramError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame solana_program_error.ProgramError)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        liftM <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame solana_program_error.ProgramError)
          residual

end NLE_Owned
