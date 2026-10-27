import PoolM_NativeCancelSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_AllocateSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS005 exact bodies. Key IDs bind pure SDK constants; data_is_empty
remains an explicit Result. No CPI or mutable SDK borrow occurs in this cut. -/
/-- [pooll_slice::require_payer_and_system_program]:
    Source: 'PoolL_lib.rs', lines 5:0-25:1
    Visibility: public -/
def payerSystem
  (system loader : solana_pubkey.Pubkey)
  (payer : solana_account_info.AccountInfo)
  (system_program_account : solana_account_info.AccountInfo) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  if payer.is_signer
  then
    if payer.is_writable
    then
      if payer.executable
      then
        let pe ←
          core.convert.IntoFrom.into
            solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
            error.PoolV1ProgramError.InvalidPayer
        ok (core.result.Result.Err pe)
      else
        let p ← ok system
        let b ←
          core.cmp.impls.PartialEqShared.ne
            solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey payer.owner p
        if b
        then
          let pe ←
            core.convert.IntoFrom.into
              solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
              error.PoolV1ProgramError.InvalidPayer
          ok (core.result.Result.Err pe)
        else
          let b1 ←
            core.cmp.impls.PartialEqShared.ne
              solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
              system_program_account.key p
          if b1
          then
            let pe ←
              core.convert.IntoFrom.into
                solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
                error.PoolV1ProgramError.InvalidSystemProgram
            ok (core.result.Result.Err pe)
          else
            let p1 ← ok loader
            let b2 ←
              core.cmp.impls.PartialEqShared.ne
                solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
                system_program_account.owner p1
            if b2
            then
              let pe ←
                core.convert.IntoFrom.into
                  solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
                  error.PoolV1ProgramError.InvalidSystemProgram
              ok (core.result.Result.Err pe)
            else
              if system_program_account.executable
              then
                if system_program_account.is_signer
                then
                  let pe ←
                    core.convert.IntoFrom.into
                      solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
                      error.PoolV1ProgramError.InvalidSystemProgram
                  ok (core.result.Result.Err pe)
                else
                  if system_program_account.is_writable
                  then
                    let pe ←
                      core.convert.IntoFrom.into
                        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
                        error.PoolV1ProgramError.InvalidSystemProgram
                    ok (core.result.Result.Err pe)
                  else ok (core.result.Result.Ok ())
              else
                let pe ←
                  core.convert.IntoFrom.into
                    solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
                    error.PoolV1ProgramError.InvalidSystemProgram
                ok (core.result.Result.Err pe)
    else
      let pe ←
        core.convert.IntoFrom.into
          solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
          error.PoolV1ProgramError.InvalidPayer
      ok (core.result.Result.Err pe)
  else
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        error.PoolV1ProgramError.InvalidPayer
    ok (core.result.Result.Err pe)

/-- [pooll_slice::PoolL_allocate_prefix]:
    Source: 'PoolL_lib.rs', lines 83:0-89:1
    Visibility: public -/
def allocatePrefix
  (readEmpty : solana_account_info.AccountInfo → Result Bool)
  (system loader : solana_pubkey.Pubkey)
  (payer : solana_account_info.AccountInfo)
  (account : solana_account_info.AccountInfo)
  (system_program_account : solana_account_info.AccountInfo) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let r ← payerSystem system loader payer system_program_account
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let p ← ok system
    let b ←
      core.cmp.impls.PartialEqShared.ne
        solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey account.owner p
    if b
    then
      let pe ←
        core.convert.IntoFrom.into
          solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
          error.PoolV1ProgramError.InvalidFreshAccount
      ok (core.result.Result.Err pe)
    else
      let b1 ← readEmpty account
      if b1
      then ok (core.result.Result.Ok ())
      else
        let pe ←
          core.convert.IntoFrom.into
            solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
            error.PoolV1ProgramError.InvalidFreshAccount
        ok (core.result.Result.Err pe)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame solana_program_error.ProgramError) residual

end AspisR1.PoolL_AllocateSource
end
