import PoolM_NativeCancelSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_VaultSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS006 native metadata prefix, exact body, canonical imported SDK types.
   SDK/PDA/borrow and enclosing handler instantiation remain separate. -/
def PoolL_vault_header
  (vault : solana_account_info.AccountInfo) (expected : solana_pubkey.Pubkey) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let b ←
    core.cmp.impls.PartialEqShared.ne
      solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey vault.key expected
  if b
  then
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        error.PoolV1ProgramError.InvalidVaultTokenAddress
    ok (core.result.Result.Err pe)
  else
    if vault.executable
    then
      let pe ←
        core.convert.IntoFrom.into
          solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
          error.PoolV1ProgramError.InvalidVaultTokenAddress
      ok (core.result.Result.Err pe)
    else
      if vault.is_signer
      then
        let pe ←
          core.convert.IntoFrom.into
            solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
            error.PoolV1ProgramError.InvalidVaultTokenAddress
        ok (core.result.Result.Err pe)
      else
        if vault.is_writable
        then ok (core.result.Result.Ok ())
        else
          let pe ←
            core.convert.IntoFrom.into
              solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
              error.PoolV1ProgramError.InvalidVaultTokenAddress
          ok (core.result.Result.Err pe)
end AspisR1.PoolL_VaultSource
end
