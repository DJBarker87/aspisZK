import AdapterRwModel
import NJU_Log
set_option autoImplicit false
noncomputable section
namespace NLM_Auth233
open Aeneas Aeneas.Std Result AdapterRw
abbrev Owned := r1_pool_adapter.owned.OwnedAccount
abbrev Key := solana_pubkey.Pubkey
abbrev PE := solana_program_error.ProgramError
abbrev PR := core.result.Result Unit PE
abbrev Master := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
abbrev Checkpoint := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
abbrev Lane := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
inductive Event where
 | readonlyBuffer (a : Owned) (reply : Result PR)
 | checkpointGuard (a : Owned) (program : Key) (writable : Bool) (reply : Result PR)
 | readonlyAccount (a : Owned) (owner : Key) (reply : Result PR)
 | distinct (accounts : Array Owned 7#usize) (reply : Result PR)
 | data (a : Owned) (reply : Result (core.result.Result (Slice U8) PE))
 | key (a : Owned) (reply : Result Key)
 | toBytes (key : Key) (reply : Result (Array U8 32#usize))
 | fromBytes (bytes : Array U8 32#usize) (reply : Result Key)
 | asRef (key : Key) (reply : Result (Slice U8))
 | decodeMaster (bytes : Slice U8) (reply : Result (core.result.Result Master PE))
 | decodeCheckpoint (bytes : Slice U8) (reply : Result (core.result.Result Checkpoint PE))
 | decodeLane (bytes : Slice U8) (reply : Result (core.result.Result Lane PE))
 | pda (seeds : Slice (Slice U8)) (program : Key) (reply : Result (core.result.Result Key solana_pubkey.PubkeyError))
 | registry (verifierProgram poolProgram : Key) (masterAccount : Owned) (master : Master)
   (registry entry : Owned) (slot : U64) (reply : Result PR)
abbrev Run (A : Type) := NJU_Log.Run Event A
def G (ops : Ops)
  (verifier_program : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
  (pool_program : solana_pubkey.Pubkey) (output_lane : Std.U8)
  (current_slot : Std.U64) :
  Run (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts
    solana_program_error.ProgramError)
  := do
  let i := Slice.len accounts
  if i = 7#usize
  then
    let proof_account ← Slice.index_usize accounts 0#usize
    let master_account ← Slice.index_usize accounts 1#usize
    let checkpoint_account ← Slice.index_usize accounts 2#usize
    let lane_account ← Slice.index_usize accounts 3#usize
    let registry_account ← Slice.index_usize accounts 4#usize
    let entry_account ← Slice.index_usize accounts 5#usize
    let verifier_checkpoint ← Slice.index_usize accounts 6#usize
    let r ← NJU_Log.record (.readonlyBuffer proof_account) (r1_pool_adapter.owned.require_readonly_buffer proof_account)
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ← NJU_Log.record (.checkpointGuard verifier_checkpoint verifier_program false) ((r1_pool_adapter.owned.require_verifier_checkpoint ops) verifier_checkpoint verifier_program false)
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r2 ← NJU_Log.record (.readonlyAccount master_account pool_program) ((r1_pool_adapter.owned.require_readonly_account ops) master_account pool_program)
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r3 ← NJU_Log.record (.readonlyAccount checkpoint_account pool_program) ((r1_pool_adapter.owned.require_readonly_account ops) checkpoint_account pool_program)
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r4 ← NJU_Log.record (.readonlyAccount lane_account pool_program) ((r1_pool_adapter.owned.require_readonly_account ops) lane_account pool_program)
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r5 ← NJU_Log.record (.distinct (Array.make 7#usize [ proof_account, master_account, checkpoint_account, lane_account, registry_account, entry_account, verifier_checkpoint ])) ((r1_pool_adapter.owned.require_distinct_accounts ops) (Array.make 7#usize [ proof_account, master_account, checkpoint_account, lane_account, registry_account, entry_account, verifier_checkpoint ]))
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r6 ← NJU_Log.record (.data master_account) ((r1_pool_adapter.owned.OwnedAccount.data ops) master_account)
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let r7 ← NJU_Log.record (.decodeMaster val) (ops.op48 val)
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val1 =>
                    let p ← NJU_Log.record (.key master_account) (r1_pool_adapter.owned.OwnedAccount.impl.key master_account)
                    let a ← NJU_Log.record (.toBytes p) (ops.op39 p)
                    let b ←
                      core.array.equality.PartialEqArray.ne
                        core.cmp.PartialEqU8 val1.identity.pool a
                    if b
                    then
                      ok (core.result.Result.Err
                        solana_program_error.ProgramError.InvalidAccountData)
                    else
                      let i1 ←
                        ops.op16
                      if val1.initialized_lane_mask != i1
                      then
                        ok (core.result.Result.Err
                          solana_program_error.ProgramError.InvalidAccountData)
                      else
                        let p1 ← NJU_Log.record (.fromBytes val1.identity.asset_mint) (ops.op37 val1.identity.asset_mint)
                        let s ← NJU_Log.record (.asRef p1) (ops.op40 p1)
                        let s1 ←
                          lift (Array.to_slice
                            (Array.make 1#usize [ val1.bump ]))
                        let s2 ←
                          lift (Array.to_slice
                            (Array.make 3#usize [
                              r1_pool_adapter.PAIR_FOREST_MASTER_SEED, s, s1
                              ]))
                        let r8 ← NJU_Log.record (.pda s2 pool_program) (ops.op38 s2 pool_program)
                        let r9 ←
                          core.result.Result.map_err
                            r1_pool_adapter.owned.authenticate_asq8_accounts.closure.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
                            r8 ()
                        let cf8 ←
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue val2 =>
                          let b1 ←
                            core.cmp.PartialEq.ne.trait_default
                              (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
                              val2 p
                          if b1
                          then
                            ok (core.result.Result.Err
                              solana_program_error.ProgramError.InvalidAccountData)
                          else
                            let r10 ← NJU_Log.record (.registry verifier_program pool_program master_account val1 registry_account entry_account current_slot) ((r1_pool_adapter.owned.authenticate_invariant_release_registry ops) verifier_program pool_program master_account val1 registry_account entry_account current_slot)
                            let cf9 ←
                              core.result.Result.Insts.CoreOpsTry.branch r10
                            match cf9 with
                            | core.ops.control_flow.ControlFlow.Continue _ =>
                              let r11 ← NJU_Log.record (.data checkpoint_account) ((r1_pool_adapter.owned.OwnedAccount.data ops) checkpoint_account)
                              let cf10 ←
                                core.result.Result.Insts.CoreOpsTry.branch r11
                              match cf10 with
                              | core.ops.control_flow.ControlFlow.Continue val3
                                =>
                                let r12 ← NJU_Log.record (.decodeCheckpoint val3) (ops.op49 val3)
                                let cf11 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r12
                                match cf11 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val4 =>
                                  let a1 ← NJU_Log.record (.toBytes p) (ops.op39 p)
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
                                      let s3 ← NJU_Log.record (.asRef p) (ops.op40 p)
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
                                      let r13 ← NJU_Log.record (.pda s6 pool_program) (ops.op38 s6 pool_program)
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
                                        let p2 ← NJU_Log.record (.key checkpoint_account) (r1_pool_adapter.owned.OwnedAccount.impl.key checkpoint_account)
                                        let b4 ←
                                          core.cmp.PartialEq.ne.trait_default
                                            (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
                                            val5 p2
                                        if b4
                                        then
                                          ok (core.result.Result.Err
                                            solana_program_error.ProgramError.InvalidAccountData)
                                        else
                                          let r15 ← NJU_Log.record (.data lane_account) ((r1_pool_adapter.owned.OwnedAccount.data ops) lane_account)
                                          let cf13 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r15
                                          match cf13 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val6 =>
                                            let r16 ← NJU_Log.record (.decodeLane val6) (ops.op50 val6)
                                            let cf14 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r16
                                            match cf14 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val7 =>
                                              let a3 ← NJU_Log.record (.toBytes p) (ops.op39 p)
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
                                                  let s7 ← NJU_Log.record (.asRef p) (ops.op40 p)
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
                                                  let r17 ← NJU_Log.record (.pda s10 pool_program) (ops.op38 s10 pool_program)
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
                                                    let p3 ← NJU_Log.record (.key lane_account) (r1_pool_adapter.owned.OwnedAccount.impl.key lane_account)
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
                                                      let a4 ← NJU_Log.record (.toBytes p) (ops.op39 p)
                                                      let a5 ← NJU_Log.record (.toBytes p) (ops.op39 p)
                                                      let a6 ← NJU_Log.record (.toBytes p2) (ops.op39 p2)
                                                      let a7 ← NJU_Log.record (.toBytes p3) (ops.op39 p3)
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
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            r1_pool_adapter.AuthenticatedAsq8Accounts
                            (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_pool_adapter.AuthenticatedAsq8Accounts
                      (core.convert.FromSame solana_program_error.ProgramError)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_pool_adapter.AuthenticatedAsq8Accounts
                    (core.convert.FromSame solana_program_error.ProgramError)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_pool_adapter.AuthenticatedAsq8Accounts
                  (core.convert.FromSame solana_program_error.ProgramError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_pool_adapter.AuthenticatedAsq8Accounts
                (core.convert.FromSame solana_program_error.ProgramError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame
            solana_program_error.ProgramError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame
          solana_program_error.ProgramError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame
        solana_program_error.ProgramError) residual
  else
    let i1 := Slice.len accounts
    if i1 < 7#usize
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.NotEnoughAccountKeys)
    else
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidArgument)

end NLM_Auth233
