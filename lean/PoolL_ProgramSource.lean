import PoolM_NativeCancelSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_ProgramSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS006 native metadata prefix, exact body, canonical imported SDK types.
   SDK/PDA/borrow and enclosing handler instantiation remain separate. -/
def require_program_account
  (account : solana_account_info.AccountInfo)
  (program_id : solana_pubkey.Pubkey) (writable : Bool) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let b ←
    core.cmp.impls.PartialEqShared.ne
      solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey account.owner
      program_id
  if b
  then
    ok (core.result.Result.Err
      AdapterRw.solana_program_error.ProgramError.IncorrectProgramId)
  else
    if account.executable
    then
      ok (core.result.Result.Err
        AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
    else
      if account.is_writable != writable
      then
        ok (core.result.Result.Err
          AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
      else ok (core.result.Result.Ok ())
end AspisR1.PoolL_ProgramSource
end
