import NND_RegistryV2PdaFactor
import NND_Entry2ValueRSL
set_option autoImplicit false
noncomputable section
namespace NND_Entry2Decode
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
def run (ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let r11 ←
    (r1_pool_adapter.owned.OwnedAccount.data ops)
      entry_account
  let cf7 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r11
  match cf7 with
  |
    core.ops.control_flow.ControlFlow.Continue
    val4 =>
    let r12 ←
      ops.op34
        val4
    let r13 ←
      AdapterRw.core.result.Result.map_err
        r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError
        r12 ()
    let cf8 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r13
    match cf8 with
    |
      core.ops.control_flow.ControlFlow.Continue
      val5 =>
      NND_Entry2Pda.run ops verifier_program p registry_program loader entry_account current_slot a6 val5
    |
      core.ops.control_flow.ControlFlow.Break
      residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        solana_program_error.ProgramError)
        residual
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      solana_program_error.ProgramError)
      residual

end NND_Entry2Decode
end
