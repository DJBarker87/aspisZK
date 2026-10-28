import NDO_JHi_Authentication
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_MasterRegistry
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

/-- Verbatim extracted authentication continuation; no successful leaf is installed. -/
def run (ops : Ops)
    (verifier_program pool_program : solana_pubkey.Pubkey) (output_lane : U8) (current_slot : U64)
    (master_account checkpoint_account lane_account registry_account entry_account : r1_pool_adapter.owned.OwnedAccount)
    (val1 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
    (p : solana_pubkey.Pubkey) :
    Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts solana_program_error.ProgramError) := do
  let r10 ←
    (r1_pool_adapter.owned.authenticate_invariant_release_registry ops)
      verifier_program pool_program master_account
      val1 registry_account entry_account
      current_slot
  let cf9 ←
    core.result.Result.Insts.CoreOpsTry.branch r10
  match cf9 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let r11 ←
      (r1_pool_adapter.owned.OwnedAccount.data ops)
        checkpoint_account
    let cf10 ←
      core.result.Result.Insts.CoreOpsTry.branch r11
    match cf10 with
    | core.ops.control_flow.ControlFlow.Continue val3
      =>
      let r12 ←
        ops.op49 val3
      let cf11 ←
        core.result.Result.Insts.CoreOpsTry.branch
          r12
      match cf11 with
      | core.ops.control_flow.ControlFlow.Continue
        val4 =>
        let a1 ← ops.op39 p
        let b2 ←
          core.array.equality.PartialEqArray.ne
            core.cmp.PartialEqU8 val4.master a1
        if b2
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)
        else
          let b3 ←
            core.array.equality.PartialEqArray.ne
              core.cmp.PartialEqU8
              val4.deployment_domain
              val1.identity.deployment_domain
          if b3
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)
          else
            let s3 ←
              ops.op40
                p
            let a2 ←
              lift (core.num.U64.to_le_bytes
                val4.checkpoint_sequence)
            let s4 ← lift (Array.to_slice a2)
            let s5 ←
              lift (Array.to_slice
                (Array.make 1#usize [ val4.bump ]))
            let s6 ←
              lift (Array.to_slice
                (Array.make 4#usize [
                  r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,
                  s3, s4, s5
                  ]))
            let r13 ←
              ops.op38
                s6 pool_program
            let r14 ←
              core.result.Result.map_err
                r1_pool_adapter.owned.authenticate_asq8_accounts.closure_1.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
                r13 ()
            let cf12 ←
              core.result.Result.Insts.CoreOpsTry.branch
                r14
            match cf12 with
            |
              core.ops.control_flow.ControlFlow.Continue
              val5 =>
              let p2 ←
                r1_pool_adapter.owned.OwnedAccount.impl.key
                  checkpoint_account
              let b4 ←
                core.cmp.PartialEq.ne.trait_default
                  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
                  val5 p2
              if b4
              then
                ok (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData)
              else
                let r15 ←
                  (r1_pool_adapter.owned.OwnedAccount.data ops)
                    lane_account
                let cf13 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r15
                match cf13 with
                |
                  core.ops.control_flow.ControlFlow.Continue
                  val6 =>
                  let r16 ←
                    ops.op50
                      val6
                  let cf14 ←
                    core.result.Result.Insts.CoreOpsTry.branch
                      r16
                  match cf14 with
                  |
                    core.ops.control_flow.ControlFlow.Continue
                    val7 =>
                    let a3 ←
                      ops.op39 p
                    let b5 ←
                      core.array.equality.PartialEqArray.ne
                        core.cmp.PartialEqU8
                        val7.master a3
                    if b5
                    then
                      ok (core.result.Result.Err
                        solana_program_error.ProgramError.InvalidAccountData)
                    else
                      if val7.lane_id != output_lane
                      then
                        ok (core.result.Result.Err
                          solana_program_error.ProgramError.InvalidAccountData)
                      else
                        let s7 ←
                          ops.op40
                            p
                        let s8 ←
                          lift (Array.to_slice
                            (Array.make 1#usize [
                              output_lane
                              ]))
                        let s9 ←
                          lift (Array.to_slice
                            (Array.make 1#usize [
                              val7.bump
                              ]))
                        let s10 ←
                          lift (Array.to_slice
                            (Array.make 4#usize [
                              r1_pool_adapter.PAIR_FOREST_LANE_SEED,
                              s7, s8, s9
                              ]))
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
                  |
                    core.ops.control_flow.ControlFlow.Break
                    residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_pool_adapter.AuthenticatedAsq8Accounts
                      (core.convert.FromSame
                      solana_program_error.ProgramError)
                      residual
                |
                  core.ops.control_flow.ControlFlow.Break
                  residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_pool_adapter.AuthenticatedAsq8Accounts
                    (core.convert.FromSame
                    solana_program_error.ProgramError)
                    residual
            | core.ops.control_flow.ControlFlow.Break
              residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_pool_adapter.AuthenticatedAsq8Accounts
                (core.convert.FromSame
                solana_program_error.ProgramError)
                residual
      | core.ops.control_flow.ControlFlow.Break
        residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_pool_adapter.AuthenticatedAsq8Accounts
          (core.convert.FromSame
          solana_program_error.ProgramError) residual
    | core.ops.control_flow.ControlFlow.Break
      residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_pool_adapter.AuthenticatedAsq8Accounts
        (core.convert.FromSame
        solana_program_error.ProgramError) residual
  | core.ops.control_flow.ControlFlow.Break residual
    =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts
      (core.convert.FromSame
      solana_program_error.ProgramError) residual
#print axioms run
end AspisR1.JHj_MasterRegistry
end
