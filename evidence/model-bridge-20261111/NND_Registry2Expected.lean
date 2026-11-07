import NND_RegistryV2ProgramFactor
import NND_Entry2ValueRSL
set_option autoImplicit false
noncomputable section
namespace NND_Registry2Expected
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
def run (ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (val2 : solana_pubkey.Pubkey) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let p1 ←
    r1_pool_adapter.owned.OwnedAccount.impl.key
      registry_account
  let b4 ←
    core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
      p1 val2
  if b4
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NND_Registry2Program.run ops verifier_program p registry_program loader master entry_account current_slot val1

end NND_Registry2Expected
end
