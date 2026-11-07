import NMX_R3_RegistryProgram
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryScript
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NMX_R3_RegistryProgram
def script (ops : Ops)
  (verifier_program : solana_pubkey.Pubkey)
  (pool_program : solana_pubkey.Pubkey)
  (master_account : r1_pool_adapter.owned.OwnedAccount)
  (master :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
  (registry_account : r1_pool_adapter.owned.OwnedAccount)
  (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : Std.U64)
  :
  Program (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let a ← scalar (ops.op39 pool_program)
  let a1 ← scalar (ops.op45)
  let b ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a a1)
  if b
  then
    pure (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    let i ← scalar (ops.op13)
    let i1 ← scalar (lift (master.verifier_policy.flags &&& i))
    if i1 = 0#u8
    then
      pure (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      let a2 ← scalar (ops.op46)
      let b1 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 master.verifier_policy.registry_program a2)
      if b1
      then
        pure (core.result.Result.Err
          solana_program_error.ProgramError.InvalidAccountData)
      else
        let a3 := Array.repeat 32#usize 0#u8
        let b2 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 master.verifier_policy.registry_authority a3)
        if b2
        then
          pure (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)
        else
          let b3 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 master.verifier_policy.policy_binding r1_pool_adapter.AUDIT_POLICY_BINDING)
          if b3
          then
            pure (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)
          else
            let r ← scalar (ops.op15 master.verifier_policy)
            let r1 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorProgramError r ())
            let cf ← scalar (core.result.Result.Insts.CoreOpsTry.branch r1)
            control cf
              (fun _ => do
                let registry_program ← scalar (ops.op37 a2)
                let r2 ← scalar ((r1_pool_adapter.owned.require_readonly_account ops) registry_account registry_program)
                let cf1 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r2)
                control cf1
                  (fun _ => do
                    let i2 ← scalar (ops.op14)
                    let i3 ← scalar (lift (master.verifier_policy.flags &&& i2))
                    if i3 != 0#u8
                    then
                      let loader ← scalar (ops.op41)
                      let r3 ← data registry_account
                      let cf2 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r3)
                      control cf2
                        (fun val => do
                          let r4 ← scalar (ops.op33 val)
                          let r5 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError r4 ())
                          let cf3 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r5)
                          control cf3
                            (fun val1 => do
                              let p ← scalar (r1_pool_adapter.owned.OwnedAccount.impl.key master_account)
                              let s ← scalar (ops.op40 p)
                              let s1 ← scalar (lift (Array.to_slice (Array.make 1#usize [ val1.bump ])))
                              let s2 ← scalar (lift (Array.to_slice (Array.make 3#usize [ r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED, s, s1 ])))
                              let r6 ← pda s2 registry_program
                              let r7 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError r6 ())
                              let cf4 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r7)
                              control cf4
                                (fun val2 => do
                                  let p1 ← scalar (r1_pool_adapter.owned.OwnedAccount.impl.key registry_account)
                                  let b4 ← scalar (core.cmp.impls.PartialEqShared.ne (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) p1 val2)
                                  if b4
                                  then
                                    pure (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let s3 ← scalar (ops.op40 registry_program)
                                    let s4 ← scalar (lift (Array.to_slice (Array.make 1#usize [ val1.programdata_bump ])))
                                    let s5 ← scalar (lift (Array.to_slice (Array.make 2#usize [ s3, s4 ])))
                                    let r8 ← pda s5 loader
                                    let r9 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_3.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError r8 ())
                                    let cf5 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r9)
                                    control cf5
                                      (fun val3 => do
                                        let a4 ← scalar (ops.op39 p)
                                        let b5 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val1.pool a4)
                                        if b5
                                        then
                                          pure (core.result.Result.Err
                                            solana_program_error.ProgramError.InvalidAccountData)
                                        else
                                          let b6 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val1.authority master.verifier_policy.registry_authority)
                                          if b6
                                          then
                                            pure (core.result.Result.Err
                                              solana_program_error.ProgramError.InvalidAccountData)
                                          else
                                            let b7 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val1.policy_binding master.verifier_policy.policy_binding)
                                            if b7
                                            then
                                              pure (core.result.Result.Err
                                                solana_program_error.ProgramError.InvalidAccountData)
                                            else
                                              let a5 ← scalar (ops.op39 registry_program)
                                              let b8 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val1.registry_program a5)
                                              if b8
                                              then
                                                pure (core.result.Result.Err
                                                  solana_program_error.ProgramError.InvalidAccountData)
                                              else
                                                let a6 ← scalar (ops.op39 loader)
                                                let b9 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val1.loader_program a6)
                                                if b9
                                                then
                                                  pure (core.result.Result.Err
                                                    solana_program_error.ProgramError.InvalidAccountData)
                                                else
                                                  let a7 ← scalar (ops.op39 val3)
                                                  let b10 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val1.programdata_address a7)
                                                  if b10
                                                  then
                                                    pure (core.result.Result.Err
                                                      solana_program_error.ProgramError.InvalidAccountData)
                                                  else
                                                    let b11 ← scalar (ops.op28 val1)
                                                    if b11
                                                    then
                                                      let b12 ← scalar (ops.op27 val1)
                                                      if b12
                                                      then
                                                        pure (core.result.Result.Err
                                                          solana_program_error.ProgramError.InvalidAccountData)
                                                      else
                                                        let r10 ← scalar ((r1_pool_adapter.owned.require_readonly_account ops) entry_account registry_program)
                                                        let cf6 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r10)
                                                        control cf6
                                                          (fun _ => do
                                                            let r11 ← data entry_account
                                                            let cf7 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r11)
                                                            control cf7
                                                              (fun val4 => do
                                                                let r12 ← scalar (ops.op34 val4)
                                                                let r13 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_4.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError r12 ())
                                                                let cf8 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r13)
                                                                control cf8
                                                                  (fun val5 => do
                                                                    let s6 ← scalar (ops.op40 p)
                                                                    let s7 ← scalar (lift (Array.to_slice r1_pool_adapter.PROFILE_BINDING))
                                                                    let s8 ← scalar (lift (Array.to_slice r1_pool_adapter.RELEASE_BINDING))
                                                                    let s9 ← scalar (lift (Array.to_slice (Array.make 1#usize [ val5.bump ])))
                                                                    let s10 ← scalar (lift (Array.to_slice (Array.make 5#usize [ r1_pool_adapter.VERIFIER_ENTRY_V2_SEED, s6, s7, s8, s9 ])))
                                                                    let r14 ← pda s10 registry_program
                                                                    let r15 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_5.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError r14 ())
                                                                    let cf9 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r15)
                                                                    control cf9
                                                                      (fun val6 => do
                                                                        let p2 ← scalar (r1_pool_adapter.owned.OwnedAccount.impl.key entry_account)
                                                                        let b13 ← scalar (core.cmp.impls.PartialEqShared.ne (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) p2 val6)
                                                                        if b13
                                                                        then
                                                                          pure
                                                                            (core.result.Result.Err
                                                                            solana_program_error.ProgramError.InvalidAccountData)
                                                                        else
                                                                          let s11 ← scalar (ops.op40 verifier_program)
                                                                          let s12 ← scalar (lift (Array.to_slice (Array.make 1#usize [ val5.programdata_bump ])))
                                                                          let s13 ← scalar (lift (Array.to_slice (Array.make 2#usize [ s11, s12 ])))
                                                                          let r16 ← pda s13 loader
                                                                          let r17 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_6.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError r16 ())
                                                                          let cf10 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r17)
                                                                          control cf10
                                                                            (fun val7 => do
                                                                              let a8 ← scalar (ops.op39 p)
                                                                              let b14 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val5.pool a8)
                                                                              if b14
                                                                              then
                                                                                pure
                                                                                  (core.result.Result.Err
                                                                                  solana_program_error.ProgramError.InvalidAccountData)
                                                                              else
                                                                                let b15 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val5.policy_binding r1_pool_adapter.AUDIT_POLICY_BINDING)
                                                                                if b15
                                                                                then
                                                                                  pure
                                                                                    (core.result.Result.Err
                                                                                    solana_program_error.ProgramError.InvalidAccountData)
                                                                                else
                                                                                  let a9 ← scalar (ops.op39 verifier_program)
                                                                                  let b16 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val5.verifier_program a9)
                                                                                  if b16
                                                                                  then
                                                                                    pure
                                                                                      (core.result.Result.Err
                                                                                      solana_program_error.ProgramError.InvalidAccountData)
                                                                                  else
                                                                                    let b17 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val5.profile_binding r1_pool_adapter.PROFILE_BINDING)
                                                                                    if b17
                                                                                    then
                                                                                      pure
                                                                                        (core.result.Result.Err
                                                                                        solana_program_error.ProgramError.InvalidAccountData)
                                                                                    else
                                                                                      let b18 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val5.release_binding r1_pool_adapter.RELEASE_BINDING)
                                                                                      if b18
                                                                                      then
                                                                                        pure
                                                                                          (core.result.Result.Err
                                                                                          solana_program_error.ProgramError.InvalidAccountData)
                                                                                      else
                                                                                        let i4 ← scalar (ops.op18)
                                                                                        if
                                                                                          val5.statement_version
                                                                                          != i4
                                                                                        then
                                                                                          pure
                                                                                            (core.result.Result.Err
                                                                                          solana_program_error.ProgramError.InvalidAccountData)
                                                                                        else
                                                                                          let b19 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val5.loader_program a6)
                                                                                          if b19
                                                                                          then
                                                                                          pure
                                                                                            (core.result.Result.Err
                                                                                            solana_program_error.ProgramError.InvalidAccountData)
                                                                                          else
                                                                                            let a10 ← scalar (ops.op39 val7)
                                                                                            let b20 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val5.programdata_address a10)
                                                                                            if b20
                                                                                            then
                                                                                            pure
                                                                                              (core.result.Result.Err
                                                                                              solana_program_error.ProgramError.InvalidAccountData)
                                                                                            else
                                                                                              let a11 :=
                                                                                                Array.repeat
                                                                                                32#usize
                                                                                                0#u8
                                                                                              let b21 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val5.expected_upgrade_authority a11)
                                                                                              if b21
                                                                                              then
                                                                                              pure
                                                                                                (core.result.Result.Err
                                                                                                solana_program_error.ProgramError.InvalidAccountData)
                                                                                              else
                                                                                                let b22 ← scalar (ops.op29 val5 current_slot)
                                                                                                if b22
                                                                                                then
                                                                                                pure
                                                                                                  (core.result.Result.Ok
                                                                                                  ())
                                                                                                else
                                                                                                  pure
                                                                                                    (core.result.Result.Err
                                                                                                    solana_program_error.ProgramError.InvalidAccountData))
                                                                            (fun residual => do
                                                                              scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                                                                      (fun residual => do
                                                                        scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                                                                  (fun residual => do
                                                                    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                                                              (fun residual => do
                                                                scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                                                          (fun residual => do
                                                            scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual))
                                                    else
                                                      pure (core.result.Result.Err
                                                        solana_program_error.ProgramError.InvalidAccountData))
                                      (fun residual => do
                                        scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                                (fun residual => do
                                  scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                            (fun residual => do
                              scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                        (fun residual => do
                          scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual))
                    else
                      let r3 ← data registry_account
                      let cf2 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r3)
                      control cf2
                        (fun val => do
                          let r4 ← scalar (ops.op31 val)
                          let r5 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_7.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError r4 ())
                          let cf3 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r5)
                          control cf3
                            (fun val1 => do
                              let p ← scalar (r1_pool_adapter.owned.OwnedAccount.impl.key master_account)
                              let s ← scalar (ops.op40 p)
                              let s1 ← scalar (lift (Array.to_slice (Array.make 1#usize [ val1.bump ])))
                              let s2 ← scalar (lift (Array.to_slice (Array.make 3#usize [ r1_pool_adapter.VERIFIER_REGISTRY_SEED, s, s1 ])))
                              let r6 ← pda s2 registry_program
                              let r7 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_8.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError r6 ())
                              let cf4 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r7)
                              control cf4
                                (fun val2 => do
                                  let p1 ← scalar (r1_pool_adapter.owned.OwnedAccount.impl.key registry_account)
                                  let b4 ← scalar (core.cmp.impls.PartialEqShared.ne (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) p1 val2)
                                  if b4
                                  then
                                    pure (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let a4 ← scalar (ops.op39 p)
                                    let b5 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val1.pool a4)
                                    if b5
                                    then
                                      pure (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData)
                                    else
                                      let b6 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val1.authority master.verifier_policy.registry_authority)
                                      if b6
                                      then
                                        pure (core.result.Result.Err
                                          solana_program_error.ProgramError.InvalidAccountData)
                                      else
                                        let b7 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val1.policy_binding master.verifier_policy.policy_binding)
                                        if b7
                                        then
                                          pure (core.result.Result.Err
                                            solana_program_error.ProgramError.InvalidAccountData)
                                        else
                                          let b8 ← scalar (ops.op26 val1)
                                          if b8
                                          then
                                            let b9 ← scalar (ops.op25 val1)
                                            if b9
                                            then
                                              pure (core.result.Result.Err
                                                solana_program_error.ProgramError.InvalidAccountData)
                                            else
                                              let r8 ← scalar ((r1_pool_adapter.owned.require_readonly_account ops) entry_account registry_program)
                                              let cf5 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r8)
                                              control cf5
                                                (fun _ => do
                                                  let r9 ← data entry_account
                                                  let cf6 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r9)
                                                  control cf6
                                                    (fun val3 => do
                                                      let r10 ← scalar (ops.op32 val3)
                                                      let r11 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_9.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError r10 ())
                                                      let cf7 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r11)
                                                      control cf7
                                                        (fun val4 => do
                                                          let s3 ← scalar (ops.op40 p)
                                                          let s4 ← scalar (lift (Array.to_slice r1_pool_adapter.PROFILE_BINDING))
                                                          let s5 ← scalar (lift (Array.to_slice r1_pool_adapter.RELEASE_BINDING))
                                                          let s6 ← scalar (lift (Array.to_slice (Array.make 1#usize [ val4.bump ])))
                                                          let s7 ← scalar (lift (Array.to_slice (Array.make 5#usize [ r1_pool_adapter.VERIFIER_ENTRY_SEED, s3, s4, s5, s6 ])))
                                                          let r12 ← pda s7 registry_program
                                                          let r13 ← scalar (core.result.Result.map_err r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_10.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError r12 ())
                                                          let cf8 ← scalar (core.result.Result.Insts.CoreOpsTry.branch r13)
                                                          control cf8
                                                            (fun val5 => do
                                                              let p2 ← scalar (r1_pool_adapter.owned.OwnedAccount.impl.key entry_account)
                                                              let b10 ← scalar (core.cmp.impls.PartialEqShared.ne (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) p2 val5)
                                                              if b10
                                                              then
                                                                pure (core.result.Result.Err
                                                                  solana_program_error.ProgramError.InvalidAccountData)
                                                              else
                                                                let a5 ← scalar (ops.op39 p)
                                                                let b11 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val4.pool a5)
                                                                if b11
                                                                then
                                                                  pure (core.result.Result.Err
                                                                    solana_program_error.ProgramError.InvalidAccountData)
                                                                else
                                                                  let b12 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val4.policy_binding r1_pool_adapter.AUDIT_POLICY_BINDING)
                                                                  if b12
                                                                  then
                                                                    pure (core.result.Result.Err
                                                                      solana_program_error.ProgramError.InvalidAccountData)
                                                                  else
                                                                    let a6 ← scalar (ops.op39 verifier_program)
                                                                    let b13 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val4.verifier_program a6)
                                                                    if b13
                                                                    then
                                                                      pure (core.result.Result.Err
                                                                        solana_program_error.ProgramError.InvalidAccountData)
                                                                    else
                                                                      let b14 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val4.profile_binding r1_pool_adapter.PROFILE_BINDING)
                                                                      if b14
                                                                      then
                                                                        pure
                                                                          (core.result.Result.Err
                                                                          solana_program_error.ProgramError.InvalidAccountData)
                                                                      else
                                                                        let b15 ← scalar (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 val4.release_binding r1_pool_adapter.RELEASE_BINDING)
                                                                        if b15
                                                                        then
                                                                          pure
                                                                            (core.result.Result.Err
                                                                            solana_program_error.ProgramError.InvalidAccountData)
                                                                        else
                                                                          let i4 ← scalar (ops.op18)
                                                                          if
                                                                            val4.statement_version
                                                                            != i4
                                                                          then
                                                                            pure
                                                                              (core.result.Result.Err
                                                                              solana_program_error.ProgramError.InvalidAccountData)
                                                                          else
                                                                            let b16 ← scalar (ops.op30 val4 current_slot)
                                                                            if b16
                                                                            then
                                                                              pure
                                                                                (core.result.Result.Ok
                                                                                ())
                                                                            else
                                                                              pure
                                                                                (core.result.Result.Err
                                                                                solana_program_error.ProgramError.InvalidAccountData))
                                                            (fun residual => do
                                                              scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                                                        (fun residual => do
                                                          scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                                                    (fun residual => do
                                                      scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                                                (fun residual => do
                                                  scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual))
                                          else
                                            pure (core.result.Result.Err
                                              solana_program_error.ProgramError.InvalidAccountData))
                                (fun residual => do
                                  scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                            (fun residual => do
                              scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                        (fun residual => do
                          scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
                  (fun residual => do
                    scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)))
              (fun residual => do
                scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual)
  )
end NMX_R3_RegistryScript
end
