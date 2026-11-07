import NMS_Emitted241
set_option autoImplicit false
noncomputable section
namespace NMS_Effect242
open Aeneas Aeneas.Std Result AdapterRw
variable {M : Type → Type} [Monad M] [MonadLift Result M]
local instance : MonadLift Result Result where
 monadLift := id
structure Effects (M : Type → Type) where
  op9 : ∀ {T : Type}, (Slice T) → M (Option T)
  op17 : (Array aspis_core.field.M31 8#usize) → M (core.result.Result Std.U8
        aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1)
  op20 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1
        → M (Array aspis_core.field.M31 8#usize)
  op23 : (Slice Std.U8) → M (core.result.Result
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  op37 : (Array Std.U8 32#usize) → M solana_pubkey.Pubkey
  op45 : M (Array Std.U8 32#usize)
  op51 : (Slice Std.U8) → M (core.result.Result
        r1_pool_adapter.ScannedAsqaProof solana_program_error.ProgramError)
  op52 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
        → r1_pool_adapter.AuthenticatedAsq8Accounts →
        aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 →
        M (core.result.Result
        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
        solana_program_error.ProgramError)
  data : r1_pool_adapter.owned.OwnedAccount → M (core.result.Result (Slice U8) solana_program_error.ProgramError)

abbrev AuthCall (M : Type → Type) := solana_pubkey.Pubkey →
 Slice r1_pool_adapter.owned.OwnedAccount → solana_pubkey.Pubkey → U8 → U64 →
 M (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts solana_program_error.ProgramError)

def validate (ops : Ops) (effects : Effects M) (auth : AuthCall M)
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

def raw (ops : Ops) : Effects Result := {
 op9 := ops.op9
 op17 := ops.op17
 op20 := ops.op20
 op23 := ops.op23
 op37 := ops.op37
 op45 := ops.op45
 op51 := ops.op51
 op52 := ops.op52
 data := NMS_Emitted.get ops
}

theorem erases (ops : Ops) (auth : NMS_Emitted.AuthCall)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 validate ops (raw ops) auth program accounts data slot =
 NMS_Emitted.validate ops auth program accounts data slot := by
 unfold validate raw NMS_Emitted.validate
 rfl
#print axioms erases
end NMS_Effect242
