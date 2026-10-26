import PoolM_NativeCancelSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_CloseSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/-- AENEAS001 body, canonical metadata; only SDK data_len is parameterized.
This is the native close rejecting prefix, not a whole-handler source join. -/
/-- [pooll_slice::PoolL_close_prefix]:
    Source: 'PoolL_lib.rs', lines 26:0-44:1
    Visibility: public -/
def closePrefix
  (readLength : solana_account_info.AccountInfo → Result Usize)
  (account : solana_account_info.AccountInfo)
  (refund_authority : solana_account_info.AccountInfo)
  (expected_owner : solana_pubkey.Pubkey) (expected_data_len : Std.Usize) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let b ←
    core.cmp.impls.PartialEqShared.ne
      solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey account.owner
      expected_owner
  if b
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    if account.executable
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      if account.is_signer
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidAccountData)
      else
        if account.is_writable
        then
          let b1 ←
            solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq
              refund_authority.key account.key
          if b1
          then
            ok (core.result.Result.Err
              solana_program_error.ProgramError.InvalidAccountData)
          else
            if refund_authority.is_writable
            then
              let i ← readLength account
              if i != expected_data_len
              then
                ok (core.result.Result.Err
                  solana_program_error.ProgramError.InvalidAccountData)
              else ok (core.result.Result.Ok ())
            else
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidAccountData)
        else
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)

#print closePrefix
end AspisR1.PoolL_CloseSource
end
