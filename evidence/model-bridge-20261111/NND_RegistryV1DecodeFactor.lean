import NND_Entry1Decode
import NND_Entry1PdaValue
set_option autoImplicit false
noncomputable section
namespace NND_RegistryV1DecodeFactor
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
def run (ops : Ops) (verifier_program pool_program : solana_pubkey.Pubkey)
 (master_account : r1_pool_adapter.owned.OwnedAccount)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (registry_program : solana_pubkey.Pubkey) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let p ←
    r1_pool_adapter.owned.OwnedAccount.impl.key
      master_account
  let s ←
    ops.op40
      p
  let s1 ←
    lift (Array.to_slice
      (Array.make 1#usize [ val1.bump ]))
  let s2 ←
    lift (Array.to_slice
      (Array.make 3#usize [
        r1_pool_adapter.VERIFIER_REGISTRY_SEED, s, s1
        ]))
  let r6 ←
    ops.op38 s2
      registry_program
  let r7 ←
    AdapterRw.core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_8.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r6 ()
  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r7
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue val2 =>
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
                  NND_Entry1Decode.run ops verifier_program p registry_program entry_account current_slot
                | core.ops.control_flow.ControlFlow.Break
                  residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame
                    solana_program_error.ProgramError)
                    residual
            else
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      solana_program_error.ProgramError) residual

theorem source (ops : Ops) (verifier_program pool_program : solana_pubkey.Pubkey)
 (master_account : r1_pool_adapter.owned.OwnedAccount)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (registry_program : solana_pubkey.Pubkey) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) :
 NND_RegistryV1PdaFactor.run ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program val1 = run ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program val1 := rfl

#print axioms source
end NND_RegistryV1DecodeFactor
end
