import Hiq_KeyLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_PoolSource
open Aeneas Aeneas.Std Result

/-- Documented pure Pubkey inequality. The source account field projections
use the canonical SDK owned metadata record; no data/borrow operation appears
in these two extracted guards. -/
def keyNe (a b : AdapterRw.solana_pubkey.Pubkey) : Result Bool := do
  let equal ← Hist_Authority.keyEq a b
  ok (!equal)

def history.require_program_account
  (account : AdapterRw.Cuts.Account)
  (program_id : AdapterRw.solana_pubkey.Pubkey) (writable : Bool) :
  Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError)
  := do
  let b ←
    keyNe account.owner
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

/-- [aspis_pool::history::require_program_owned]:
    Source: 'programs/aspis-pool/src/history.rs', lines 66:0-77:1 -/
def history.require_program_owned
  (account : AdapterRw.Cuts.Account)
  (program_id : AdapterRw.solana_pubkey.Pubkey) :
  Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError)
  := do
  let b ←
    keyNe account.owner
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
    else ok (core.result.Result.Ok ())

end AspisR1.Hiq_PoolSource

end
