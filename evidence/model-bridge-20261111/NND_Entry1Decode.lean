import NND_RegistryV1PdaFactor
import NND_Entry1PdaValue
set_option autoImplicit false
noncomputable section
namespace NND_Entry1Decode
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
def run (ops : Ops) (verifier_program p registry_program : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let r9 ←
    (r1_pool_adapter.owned.OwnedAccount.data ops)
      entry_account
  let cf6 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r9
  match cf6 with
  |
    core.ops.control_flow.ControlFlow.Continue
    val3 =>
    let r10 ←
      ops.op32
        val3
    let r11 ←
      AdapterRw.core.result.Result.map_err
        r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_9.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError
        r10 ()
    let cf7 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r11
    match cf7 with
    |
      core.ops.control_flow.ControlFlow.Continue
      val4 =>
      NND_Entry1Pda.run ops verifier_program p registry_program entry_account current_slot val4
    |
      core.ops.control_flow.ControlFlow.Break
      residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        solana_program_error.ProgramError)
        residual
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      solana_program_error.ProgramError)
      residual

end NND_Entry1Decode
end
