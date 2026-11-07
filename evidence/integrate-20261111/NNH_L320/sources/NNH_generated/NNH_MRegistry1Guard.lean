import NNH_MRegistryV1ReadonlyFactor
import NNH_MRegistryFlagValues
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry1Guard
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
def run (ops : Ops) (verifier_program p registry_program : solana_pubkey.Pubkey)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) (val2 : solana_pubkey.Pubkey) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
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
    let a4 ← ops.op39 p
    let b5 ←
      core.array.equality.PartialEqArray.ne
        core.cmp.PartialEqU8 val1.pool a4
    if b5
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      let b6 ←
        core.array.equality.PartialEqArray.ne
          core.cmp.PartialEqU8 val1.authority
          master.verifier_policy.registry_authority
      if b6
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidAccountData)
      else
        let b7 ←
          core.array.equality.PartialEqArray.ne
            core.cmp.PartialEqU8 val1.policy_binding
            master.verifier_policy.policy_binding
        if b7
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)
        else
          let b8 ←
            ops.op26
              val1
          if b8
          then
            let b9 ←
              ops.op25
                val1
            if b9
            then
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData)
            else
              NNH_MEntry1Readonly.run ops verifier_program p registry_program entry_account current_slot
          else
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)

end NNH_MRegistry1Guard
end
