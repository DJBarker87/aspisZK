import NNH_MRegistryV1DecodeFactor
import NNH_MEntry1DecodedValue
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry1Readonly
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
def run (ops : Ops) (verifier_program p registry_program : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let r8 ←
    (r1_pool_adapter.owned.require_readonly_account ops)
      entry_account registry_program
  let cf5 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r8
  match cf5 with
  |
    core.ops.control_flow.ControlFlow.Continue
    _ =>
    NNH_MEntry1Decode.run ops verifier_program p registry_program entry_account current_slot
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      solana_program_error.ProgramError)
      residual

end NNH_MEntry1Readonly
end
