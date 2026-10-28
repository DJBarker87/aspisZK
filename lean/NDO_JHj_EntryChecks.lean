import NDO_JHi_Authentication
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_EntryChecks
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

/-- Verbatim immutable-registry caller continuation. No leaf association is assumed by this definition. -/
def run (ops : Ops)
    (verifier_program pool_program : solana_pubkey.Pubkey)
    (master_account : r1_pool_adapter.owned.OwnedAccount)
    (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
    (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
    (registry_program : solana_pubkey.Pubkey)
    (loader : solana_pubkey.Pubkey)
    (p : solana_pubkey.Pubkey)
    (a6 : Array U8 32#usize)
    (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2)
    (val7 : solana_pubkey.Pubkey) :
    Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let a8 ←
    ops.op39
      p
  let b14 ←
    core.array.equality.PartialEqArray.ne
      core.cmp.PartialEqU8
      val5.pool a8
  if b14
  then
    ok
      (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    let b15 ←
      core.array.equality.PartialEqArray.ne
        core.cmp.PartialEqU8
        val5.policy_binding
        r1_pool_adapter.AUDIT_POLICY_BINDING
    if b15
    then
      ok
        (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      let a9 ←
        ops.op39
          verifier_program
      let b16 ←
        core.array.equality.PartialEqArray.ne
          core.cmp.PartialEqU8
          val5.verifier_program
          a9
      if b16
      then
        ok
          (core.result.Result.Err
          solana_program_error.ProgramError.InvalidAccountData)
      else
        let b17 ←
          core.array.equality.PartialEqArray.ne
            core.cmp.PartialEqU8
            val5.profile_binding
            r1_pool_adapter.PROFILE_BINDING
        if b17
        then
          ok
            (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)
        else
          let b18 ←
            core.array.equality.PartialEqArray.ne
              core.cmp.PartialEqU8
              val5.release_binding
              r1_pool_adapter.RELEASE_BINDING
          if b18
          then
            ok
              (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)
          else
            let i4 ←
              ops.op18
            if
              val5.statement_version
              != i4
            then
              ok
                (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)
            else
              let b19 ←
                core.array.equality.PartialEqArray.ne
                core.cmp.PartialEqU8
                val5.loader_program
                a6
              if b19
              then
              ok
                (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData)
              else
                let a10 ←
                  ops.op39
                  val7
                let b20 ←
                  core.array.equality.PartialEqArray.ne
                  core.cmp.PartialEqU8
                  val5.programdata_address
                  a10
                if b20
                then
                ok
                  (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData)
                else
                  let a11 :=
                    Array.repeat
                    32#usize
                    0#u8
                  let b21 ←
                    core.array.equality.PartialEqArray.ne
                    core.cmp.PartialEqU8
                    val5.expected_upgrade_authority
                    a11
                  if b21
                  then
                  ok
                    (core.result.Result.Err
                    solana_program_error.ProgramError.InvalidAccountData)
                  else
                    let b22 ←
                      ops.op29
                      val5
                      current_slot
                    if b22
                    then
                    ok
                      (core.result.Result.Ok
                      ())
                    else
                      ok
                        (core.result.Result.Err
                        solana_program_error.ProgramError.InvalidAccountData)
#print axioms run
end AspisR1.JHj_EntryChecks
end
