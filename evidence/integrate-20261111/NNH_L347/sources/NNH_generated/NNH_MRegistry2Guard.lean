import NNH_MRegistryV2ReadonlyFactor
import NNH_MEntry2ValueRSL
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry2Guard
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
def run (ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (val3 : solana_pubkey.Pubkey) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
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
        let a5 ←
          ops.op39
            registry_program
        let b8 ←
          core.array.equality.PartialEqArray.ne
            core.cmp.PartialEqU8
            val1.registry_program a5
        if b8
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)
        else
          let a6 ←
            ops.op39 loader
          let b9 ←
            core.array.equality.PartialEqArray.ne
              core.cmp.PartialEqU8
              val1.loader_program a6
          if b9
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)
          else
            let a7 ←
              ops.op39 val3
            let b10 ←
              core.array.equality.PartialEqArray.ne
                core.cmp.PartialEqU8
                val1.programdata_address a7
            if b10
            then
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData)
            else
              let b11 ←
                ops.op28
                  val1
              if b11
              then
                let b12 ←
                  ops.op27
                    val1
                if b12
                then
                  ok (core.result.Result.Err
                    solana_program_error.ProgramError.InvalidAccountData)
                else
                  NNH_MEntry2Readonly.run ops verifier_program p registry_program loader entry_account current_slot a6
              else
                ok (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData)

end NNH_MRegistry2Guard
end
