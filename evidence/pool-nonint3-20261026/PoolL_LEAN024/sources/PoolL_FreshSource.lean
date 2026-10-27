import PoolM_NativeCancelSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_FreshSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS006 native metadata prefix, exact body, canonical imported SDK types.
   SDK/PDA/borrow and enclosing handler instantiation remain separate. -/
def PoolL_fresh_header
  (account : solana_account_info.AccountInfo)
  (expected_address : solana_pubkey.Pubkey) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let b ←
    core.cmp.impls.PartialEqShared.ne
      solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey account.key
      expected_address
  if b
  then
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        error.PoolV1ProgramError.InvalidFreshAccount
    ok (core.result.Result.Err pe)
  else
    if account.executable
    then
      let pe ←
        core.convert.IntoFrom.into
          solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
          error.PoolV1ProgramError.InvalidFreshAccount
      ok (core.result.Result.Err pe)
    else
      if account.is_signer
      then
        let pe ←
          core.convert.IntoFrom.into
            solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
            error.PoolV1ProgramError.InvalidFreshAccount
        ok (core.result.Result.Err pe)
      else
        if account.is_writable
        then ok (core.result.Result.Ok ())
        else
          let pe ←
            core.convert.IntoFrom.into
              solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
              error.PoolV1ProgramError.InvalidFreshAccount
          ok (core.result.Result.Err pe)
end AspisR1.PoolL_FreshSource
end
