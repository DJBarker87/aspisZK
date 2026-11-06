import NLM_Auth233
set_option autoImplicit false
noncomputable section
namespace NLM_Validate242
open Aeneas Aeneas.Std Result AdapterRw
open NLM_Auth233
abbrev Request := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Payment := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1
abbrev Candidate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
inductive Event where
 | decode (bytes : Slice U8) (reply : Result (core.result.Result Request aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))
 | poolId (reply : Result (Array U8 32#usize))
 | fromBytes (bytes : Array U8 32#usize) (reply : Result Key)
 | nullifier (payment : Payment) (reply : Result (Array aspis_core.field.M31 8#usize))
 | outputLane (nullifier : Array aspis_core.field.M31 8#usize)
   (reply : Result (core.result.Result U8 aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1))
 | authenticate (program : Key) (accounts : Slice Owned) (pool : Key) (lane : U8) (slot : U64)
   (run : NJU_Log.Run NLM_Auth233.Event (core.result.Result Auth PE))
 | data (account : Owned) (reply : Result (core.result.Result (Slice U8) PE))
 | scan (bytes : Slice U8) (reply : Result (core.result.Result r1_pool_adapter.ScannedAsqaProof PE))
 | reconstruct (request : Request) (auth : Auth) (candidate : Candidate)
   (reply : Result (core.result.Result Statement PE))
abbrev Run (A : Type) := NJU_Log.Run Event A
/-- Nested source occurrence retains the COMPLETE child's chronological Run. -/
def authenticate (ops : Ops) (program : Key) (accounts : Slice Owned)
 (pool : Key) (lane : U8) (slot : U64) : Run (core.result.Result Auth PE) :=
 let child := NLM_Auth233.G ops program accounts pool lane slot
 ⟨child.result,[.authenticate program accounts pool lane slot child]⟩
def G (ops : Ops)
  (verifier_program : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
  (instruction_data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  Run (core.result.Result r1_pool_adapter.ValidatedAsqa
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
                let r4 ←
                  authenticate ops verifier_program accounts pool_program val1 val2
                let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf3 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let o ← ops.op9 accounts
                  let r5 ←
                    core.option.Option.ok_or o
                      solana_program_error.ProgramError.NotEnoughAccountKeys
                  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf4 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let r6 ← NJU_Log.record (.data val4) ((r1_pool_adapter.owned.OwnedAccount.data ops) val4)
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let r7 ← NJU_Log.record (.scan val5) (ops.op51 val5)
                      let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf6 with
                      | core.ops.control_flow.ControlFlow.Continue val6 =>
                        let r8 ← NJU_Log.record (.reconstruct val val3 val6.candidate_afterstate) (ops.op52 val val3 val6.candidate_afterstate)
                        let cf7 ←
                          core.result.Result.Insts.CoreOpsTry.branch r8
                        match cf7 with
                        | core.ops.control_flow.ControlFlow.Continue val7 =>
                          ok (core.result.Result.Ok
                            {
                              statement := val7,
                              proof_length := val6.proof_length
                            })
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            r1_pool_adapter.ValidatedAsqa
                            (core.convert.FromSame
                            solana_program_error.ProgramError) residual
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
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
        solana_program_error.ProgramError) residual

end NLM_Validate242
