import NDO_JHi_Authentication
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_EntryRead
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
    (a6 : Array U8 32#usize) :
    Result (core.result.Result Unit solana_program_error.ProgramError) := do
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
#print axioms run
end AspisR1.JHj_EntryRead
end
