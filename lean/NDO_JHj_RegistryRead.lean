import NDO_JHi_Authentication
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_RegistryRead
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

/-- Verbatim immutable-registry caller continuation. No leaf association is assumed by this definition. -/
def run (ops : Ops)
    (verifier_program pool_program : solana_pubkey.Pubkey)
    (master_account : r1_pool_adapter.owned.OwnedAccount)
    (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
    (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
    (registry_program : solana_pubkey.Pubkey)
    (loader : solana_pubkey.Pubkey) :
    Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let r3 ←
    (r1_pool_adapter.owned.OwnedAccount.data ops) registry_account
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r4 ←
      ops.op33
        val
    let r5 ←
      core.result.Result.map_err
        r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError
        r4 ()
    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf3 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
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
        core.result.Result.map_err
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
          let s3 ←
            ops.op40
              registry_program
          let s4 ←
            lift (Array.to_slice
              (Array.make 1#usize [ val1.programdata_bump ]))
          let s5 ←
            lift (Array.to_slice
              (Array.make 2#usize [ s3, s4 ]))
          let r8 ←
            ops.op38 s5
              loader
          let r9 ←
            core.result.Result.map_err
              r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_3.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
              r8 ()
          let cf5 ←
            core.result.Result.Insts.CoreOpsTry.branch r9
          match cf5 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
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
                            let r10 ←
                              (r1_pool_adapter.owned.require_readonly_account ops)
                                entry_account registry_program
                            let cf6 ←
                              core.result.Result.Insts.CoreOpsTry.branch
                                r10
                            match cf6 with
                            |
                              core.ops.control_flow.ControlFlow.Continue
                              _ =>
                              let r11 ←
                                (r1_pool_adapter.owned.OwnedAccount.data ops)
                                  entry_account
                              let cf7 ←
                                core.result.Result.Insts.CoreOpsTry.branch
                                  r11
                              match cf7 with
                              |
                                core.ops.control_flow.ControlFlow.Continue
                                val4 =>
                                let r12 ←
                                  ops.op34
                                    val4
                                let r13 ←
                                  core.result.Result.map_err
                                    r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError
                                    r12 ()
                                let cf8 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r13
                                match cf8 with
                                |
                                  core.ops.control_flow.ControlFlow.Continue
                                  val5 =>
                                  let s6 ←
                                    ops.op40
                                      p
                                  let s7 ←
                                    lift (Array.to_slice
                                      r1_pool_adapter.PROFILE_BINDING)
                                  let s8 ←
                                    lift (Array.to_slice
                                      r1_pool_adapter.RELEASE_BINDING)
                                  let s9 ←
                                    lift (Array.to_slice
                                      (Array.make 1#usize [
                                        val5.bump
                                        ]))
                                  let s10 ←
                                    lift (Array.to_slice
                                      (Array.make 5#usize [
                                        r1_pool_adapter.VERIFIER_ENTRY_V2_SEED,
                                        s6, s7, s8, s9
                                        ]))
                                  let r14 ←
                                    ops.op38
                                      s10 registry_program
                                  let r15 ←
                                    core.result.Result.map_err
                                      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_5.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
                                      r14 ()
                                  let cf9 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r15
                                  match cf9 with
                                  |
                                    core.ops.control_flow.ControlFlow.Continue
                                    val6 =>
                                    let p2 ←
                                      r1_pool_adapter.owned.OwnedAccount.impl.key
                                        entry_account
                                    let b13 ←
                                      core.cmp.impls.PartialEqShared.ne
                                        (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
                                        p2 val6
                                    if b13
                                    then
                                      ok
                                        (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData)
                                    else
                                      let s11 ←
                                        ops.op40
                                          verifier_program
                                      let s12 ←
                                        lift (Array.to_slice
                                          (Array.make 1#usize [
                                            val5.programdata_bump
                                            ]))
                                      let s13 ←
                                        lift (Array.to_slice
                                          (Array.make 2#usize [
                                            s11, s12
                                            ]))
                                      let r16 ←
                                        ops.op38
                                          s13 loader
                                      let r17 ←
                                        core.result.Result.map_err
                                          r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_6.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError
                                          r16 ()
                                      let cf10 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r17
                                      match cf10 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val7 =>
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
                                      |
                                        core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          Unit
                                          (core.convert.FromSame
                                          solana_program_error.ProgramError)
                                          residual
                                  |
                                    core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      Unit
                                      (core.convert.FromSame
                                      solana_program_error.ProgramError)
                                      residual
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
                            |
                              core.ops.control_flow.ControlFlow.Break
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
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame
          solana_program_error.ProgramError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        solana_program_error.ProgramError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      solana_program_error.ProgramError) residual
#print axioms run
end AspisR1.JHj_RegistryRead
end
