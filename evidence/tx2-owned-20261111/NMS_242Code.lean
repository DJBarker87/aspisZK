import NMS_Effect242Fold
set_option autoImplicit false
noncomputable section
namespace NMS_242Code
open Aeneas Aeneas.Std Result AdapterRw
open NMS_Effect242 (Effects AuthCall)
variable {M : Type → Type} [Monad M] [MonadLift Result M]
def body (effects : Effects M) (auth : AuthCall M)
  (verifier_program : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
  (instruction_data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  M (core.result.Result r1_pool_adapter.ValidatedAsqa
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
    let r ←
      effects.op23
        instruction_data
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
          let a ← effects.op45
          let b2 ←
            core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
              val.pool_program a
          if b2
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidInstructionData)
          else
            let pool_program ←
              effects.op37 val.pool_program
            let a1 ←
              effects.op20
                val.«public»
            let r2 ←
              effects.op17
                a1
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
                  auth
                    verifier_program accounts pool_program val1 val2
                let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf3 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let o ← effects.op9 accounts
                  let r5 ←
                    core.option.Option.ok_or o
                      solana_program_error.ProgramError.NotEnoughAccountKeys
                  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf4 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let r6 ← effects.data val4
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let r7 ← effects.op51 val5
                      let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf6 with
                      | core.ops.control_flow.ControlFlow.Continue val6 =>
                        let r8 ←
                          effects.op52 val val3
                            val6.candidate_afterstate
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

theorem emitted (ops : Ops) (effects : Effects M) (auth : AuthCall M)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 body effects auth program accounts data slot =
 NMS_Effect242.validate ops effects auth program accounts data slot := rfl

/-- Program/account arguments are fixed at the original parent inputs at
EVERY authenticate occurrence, including runs with earlier child effects. -/
theorem auth_arguments (effects : Effects M) (auth : AuthCall M)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 body effects (fun _ _ pool lane current => auth program accounts pool lane current)
  program accounts data slot = body effects auth program accounts data slot := rfl
#print axioms emitted
#print axioms auth_arguments
end NMS_242Code
