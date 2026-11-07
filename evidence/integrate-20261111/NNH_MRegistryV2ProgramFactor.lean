import NNH_MRegistry2Program
import NNH_MEntry2ValueRSL
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryV2ProgramFactor
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
def run (ops : Ops) (verifier_program pool_program : solana_pubkey.Pubkey)
 (master_account : r1_pool_adapter.owned.OwnedAccount)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (registry_program : solana_pubkey.Pubkey) (loader : solana_pubkey.Pubkey) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
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
        r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED, s, s1
        ]))
  let r6 ←
    ops.op38 s2
      registry_program
  let r7 ←
    AdapterRw.core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
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
      NNH_MRegistry2Program.run ops verifier_program p registry_program loader master entry_account current_slot val1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      solana_program_error.ProgramError) residual

theorem source (ops : Ops) (verifier_program pool_program : solana_pubkey.Pubkey)
 (master_account : r1_pool_adapter.owned.OwnedAccount)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (registry_program : solana_pubkey.Pubkey) (loader : solana_pubkey.Pubkey) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) :
 NNH_MRegistryV2GuardFactor.run ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program loader val1 = run ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program loader val1 := rfl

#print axioms source
end NNH_MRegistryV2ProgramFactor
end
