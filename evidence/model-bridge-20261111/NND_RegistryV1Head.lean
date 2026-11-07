import NND_RegistryBranches
import NND_FormatControl
set_option autoImplicit false
noncomputable section
namespace NND_RegistryV1Head
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
def decoded (ops : Ops) (verifier_program pool_program : solana_pubkey.Pubkey)
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
                  let r9 ←
                    (r1_pool_adapter.owned.OwnedAccount.data ops)
                      entry_account
                  let cf6 ←
                    core.result.Result.Insts.CoreOpsTry.branch
                      r9
                  match cf6 with
                  |
                    core.ops.control_flow.ControlFlow.Continue
                    val3 =>
                    let r10 ←
                      ops.op32
                        val3
                    let r11 ←
                      AdapterRw.core.result.Result.map_err
                        r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_9.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError
                        r10 ()
                    let cf7 ←
                      core.result.Result.Insts.CoreOpsTry.branch
                        r11
                    match cf7 with
                    |
                      core.ops.control_flow.ControlFlow.Continue
                      val4 =>
                      let s3 ←
                        ops.op40
                          p
                      let s4 ←
                        lift (Array.to_slice
                          r1_pool_adapter.PROFILE_BINDING)
                      let s5 ←
                        lift (Array.to_slice
                          r1_pool_adapter.RELEASE_BINDING)
                      let s6 ←
                        lift (Array.to_slice
                          (Array.make 1#usize [
                            val4.bump
                            ]))
                      let s7 ←
                        lift (Array.to_slice
                          (Array.make 5#usize [
                            r1_pool_adapter.VERIFIER_ENTRY_SEED,
                            s3, s4, s5, s6
                            ]))
                      let r12 ←
                        ops.op38
                          s7 registry_program
                      let r13 ←
                        AdapterRw.core.result.Result.map_err
                          r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_10.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
                          r12 ()
                      let cf8 ←
                        core.result.Result.Insts.CoreOpsTry.branch
                          r13
                      match cf8 with
                      |
                        core.ops.control_flow.ControlFlow.Continue
                        val5 =>
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
                      |
                        core.ops.control_flow.ControlFlow.Break
                        residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          Unit (core.convert.FromSame
                          solana_program_error.ProgramError)
                          residual
                    |
                      core.ops.control_flow.ControlFlow.Break
                      residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Unit (core.convert.FromSame
                        solana_program_error.ProgramError)
                        residual
                  | core.ops.control_flow.ControlFlow.Break
                    residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      Unit (core.convert.FromSame
                      solana_program_error.ProgramError)
                      residual
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

def run (ops : Ops) (verifier_program pool_program : solana_pubkey.Pubkey)
 (master_account : r1_pool_adapter.owned.OwnedAccount)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (registry_program : solana_pubkey.Pubkey) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let r3 ←
    (r1_pool_adapter.owned.OwnedAccount.data ops) registry_account
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r4 ←
      ops.op31
        val
    let r5 ←
      AdapterRw.core.result.Result.map_err
        r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_7.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError
        r4 ()
    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf3 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      decoded ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program val1
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        solana_program_error.ProgramError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      solana_program_error.ProgramError) residual

theorem source (ops : Ops) (v p : solana_pubkey.Pubkey)
 (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey) :
 NND_RegistryBranches.v1 ops v p m s r e t rp = run ops v p m s r e t rp := rfl

#print axioms source
end NND_RegistryV1Head
end
