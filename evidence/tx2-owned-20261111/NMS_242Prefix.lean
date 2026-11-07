import NMS_242Auth
set_option autoImplicit false
noncomputable section
namespace NMS_242Prefix
open Aeneas Aeneas.Std Result AdapterRw NMS_OwnedPackets NMS_RowSpec242
variable {Ambient : Type}
def owned (ops : Ops) (child : NMS_RowSpec233.Native Ambient)
 (before : World Ambient) (inputOwners : List Nat)
  (verifier_program : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
  (instruction_data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  NMS_Owned242.Run Ambient (core.result.Result Validated
    solana_program_error.ProgramError)
  := do
  let i := Slice.len instruction_data
  let i1 ←
    aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  if i != i1
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let r ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.decode instruction_data reply) (by trivial)) (ops.op23 instruction_data)
    let r1 ←
      core.result.Result.map_err
        r1_pool_adapter.owned.validate_asq8.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let b ←
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
          val.verifier_profile r1_pool_adapter.PROFILE_BINDING
      if b
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidInstructionData)
      else
        let b1 ←
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
            val.verifier_release r1_pool_adapter.RELEASE_BINDING
        if b1
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidInstructionData)
        else
          let a ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.poolId reply) (by trivial)) (ops.op45)
          let b2 ←
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
              val.pool_program a
          if b2
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidInstructionData)
          else
            let pool_program ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.fromBytes val.pool_program reply) (by trivial)) (ops.op37 val.pool_program)
            let a1 ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.nullifier val.«public» reply) (by trivial)) (ops.op20 val.«public»)
            let r2 ← NJU_Log.record (fun reply => Event.plain (NLM_Validate242.Event.outputLane a1 reply) (by trivial)) (ops.op17 a1)
            let r3 ←
              core.result.Result.map_err
                r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
                r2 ()
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue val1 =>
              let cf2 ←
                core.result.Result.Insts.CoreOpsTry.branch current_slot
              match cf2 with
              | core.ops.control_flow.ControlFlow.Continue val2 =>
                NMS_242Auth.owned ops child before inputOwners val verifier_program accounts pool_program val1 val2
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Validated (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Validated (core.convert.FromSame
                solana_program_error.ProgramError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Validated (core.convert.FromSame
        solana_program_error.ProgramError) residual

def raw (ops : Ops)
  (verifier_program : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
  (instruction_data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  NJU_Log.Run RawEvent (core.result.Result r1_pool_adapter.ValidatedAsqa
    solana_program_error.ProgramError)
  := do
  let i := Slice.len instruction_data
  let i1 ←
    aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  if i != i1
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let r ← NJU_Log.record (.decode instruction_data) (ops.op23 instruction_data)
    let r1 ←
      core.result.Result.map_err
        r1_pool_adapter.owned.validate_asq8.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let b ←
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
          val.verifier_profile r1_pool_adapter.PROFILE_BINDING
      if b
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidInstructionData)
      else
        let b1 ←
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
            val.verifier_release r1_pool_adapter.RELEASE_BINDING
        if b1
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidInstructionData)
        else
          let a ← NJU_Log.record (.poolId) (ops.op45)
          let b2 ←
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
              val.pool_program a
          if b2
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidInstructionData)
          else
            let pool_program ← NJU_Log.record (.fromBytes val.pool_program) (ops.op37 val.pool_program)
            let a1 ← NJU_Log.record (.nullifier val.«public») (ops.op20 val.«public»)
            let r2 ← NJU_Log.record (.outputLane a1) (ops.op17 a1)
            let r3 ←
              core.result.Result.map_err
                r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
                r2 ()
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue val1 =>
              let cf2 ←
                core.result.Result.Insts.CoreOpsTry.branch current_slot
              match cf2 with
              | core.ops.control_flow.ControlFlow.Continue val2 =>
                NMS_242Auth.raw ops val verifier_program accounts pool_program val1 val2
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
                solana_program_error.ProgramError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
        solana_program_error.ProgramError) residual

end NMS_242Prefix
