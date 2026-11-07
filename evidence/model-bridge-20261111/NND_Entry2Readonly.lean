import NND_RegistryV2DecodeFactor
import NND_Entry2ValueRSL
set_option autoImplicit false
noncomputable section
namespace NND_Entry2Readonly
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
def run (ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let r10 ←
    (r1_pool_adapter.owned.require_readonly_account ops)
      entry_account registry_program
  let cf6 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r10
  match cf6 with
  |
    core.ops.control_flow.ControlFlow.Continue
    _ =>
    NND_Entry2Decode.run ops verifier_program p registry_program loader entry_account current_slot a6
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      solana_program_error.ProgramError)
      residual

end NND_Entry2Readonly
end
