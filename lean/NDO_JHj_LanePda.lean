import NDO_JHi_Authentication
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_LanePda
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

/-- Verbatim extracted authentication continuation; no successful leaf is installed. -/
def run (ops : Ops)
    (verifier_program pool_program : solana_pubkey.Pubkey) (output_lane : U8) (current_slot : U64)
    (master_account checkpoint_account lane_account registry_account entry_account : r1_pool_adapter.owned.OwnedAccount)
    (val1 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
    (p : solana_pubkey.Pubkey)
    (val4 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) (p2 : solana_pubkey.Pubkey)
    (val7 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1) (s10 : Slice (Slice U8)) :
    Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts solana_program_error.ProgramError) := do
  let r17 ←
    ops.op38
      s10 pool_program
  let r18 ←
    core.result.Result.map_err
      r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
      r17 ()
  let cf15 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r18
  match cf15 with
  |
    core.ops.control_flow.ControlFlow.Continue
    val8 =>
    let p3 ←
      r1_pool_adapter.owned.OwnedAccount.impl.key
        lane_account
    let b6 ←
      core.cmp.PartialEq.ne.trait_default
        (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
        val8 p3
    if b6
    then
      ok
        (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      let a4 ←
        ops.op39
          p
      let a5 ←
        ops.op39
          p
      let a6 ←
        ops.op39
          p2
      let a7 ←
        ops.op39
          p3
      ok (core.result.Result.Ok
        {
          master_account := a5,
          checkpoint_account :=
            a6,
          selected_lane_account :=
            a7,
          master := val1,
          checkpoint := val4,
          selected_lane := val7,
          live_snapshot :=
            {
              pool := a4,
              deployment_domain :=
                val1.identity.deployment_domain,
              sequence :=
                val7.tree.next_leaf_index,
              next_pair_index :=
                val7.tree.next_leaf_index,
              current_root :=
                val7.tree.root,
              frontier :=
                val7.tree.frontier
            }
        })
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame
      solana_program_error.ProgramError)
      residual
#print axioms run
end AspisR1.JHj_LanePda
end
