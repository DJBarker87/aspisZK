import NND_RegistryV2ProgramdataFactor
import NND_Entry2ValueRSL
set_option autoImplicit false
noncomputable section
namespace NND_Entry2Expected
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
def run (ops : Ops) (verifier_program p loader : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize)
 (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (val6 : solana_pubkey.Pubkey) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let p2 ←
    r1_pool_adapter.owned.OwnedAccount.impl.key
      entry_account
  let b13 ←
    core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
      p2 val6
  if b13
  then
    ok
      (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    NND_Entry2Programdata.run ops verifier_program p loader current_slot a6 val5

end NND_Entry2Expected
end
