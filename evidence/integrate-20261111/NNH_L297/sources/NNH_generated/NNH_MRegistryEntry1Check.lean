import NNH_MRegistryV1Head
import NNH_MRegistryScalarOps
import NNH_MEntryRecordGuards
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryEntry1Check
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
def check (ops : Ops) (verifier_program p : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) (val5 : solana_pubkey.Pubkey) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let p2 ←
    r1_pool_adapter.owned.OwnedAccount.impl.key
      entry_account
  let b10 ←
    core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
      p2 val5
  if b10
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    let a5 ←
      ops.op39 p
    let b11 ←
      core.array.equality.PartialEqArray.ne
        core.cmp.PartialEqU8
        val4.pool a5
    if b11
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      let b12 ←
        core.array.equality.PartialEqArray.ne
          core.cmp.PartialEqU8
          val4.policy_binding
          r1_pool_adapter.AUDIT_POLICY_BINDING
      if b12
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidAccountData)
      else
        let a6 ←
          ops.op39
            verifier_program
        let b13 ←
          core.array.equality.PartialEqArray.ne
            core.cmp.PartialEqU8
            val4.verifier_program a6
        if b13
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)
        else
          let b14 ←
            core.array.equality.PartialEqArray.ne
              core.cmp.PartialEqU8
              val4.profile_binding
              r1_pool_adapter.PROFILE_BINDING
          if b14
          then
            ok
              (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)
          else
            let b15 ←
              core.array.equality.PartialEqArray.ne
                core.cmp.PartialEqU8
                val4.release_binding
                r1_pool_adapter.RELEASE_BINDING
            if b15
            then
              ok
                (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData)
            else
              let i4 ←
                ops.op18
              if
                val4.statement_version
                != i4
              then
                ok
                  (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData)
              else
                let b16 ←
                  ops.op30
                    val4 current_slot
                if b16
                then
                  ok
                    (core.result.Result.Ok
                    ())
                else
                  ok
                    (core.result.Result.Err
                    solana_program_error.ProgramError.InvalidAccountData)

end NNH_MRegistryEntry1Check
end
