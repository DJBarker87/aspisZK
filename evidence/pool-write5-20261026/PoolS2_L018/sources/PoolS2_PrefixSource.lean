import Hiq_PoolSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PrefixSource
open Aeneas Aeneas.Std Result
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Error := AdapterRw.solana_program_error.ProgramError

def systemId : Key := Array.repeat 32#usize 0#u8
def nativeLoaderId : Key := Array.make 32#usize [5#u8,135#u8,132#u8,191#u8,20#u8,139#u8,164#u8,40#u8,47#u8,176#u8,18#u8,87#u8,72#u8,136#u8,169#u8,241#u8,83#u8,160#u8,125#u8,173#u8,247#u8,101#u8,192#u8,69#u8,92#u8,154#u8,151#u8,3#u8,128#u8,0#u8,0#u8,0#u8]
def invalidPayer : Error := .Custom 1095966772#u32
def invalidSystem : Error := .Custom 1095966771#u32

/-- Original emitted guards with canonical metadata owner and documented pure
key inequality/SDK IDs/error conversion. No borrow/CPI/caller law is supplied. -/
def pair_forest.require_exact_account_count
  (accounts : Slice Account) (expected : Std.Usize) :
  Result (core.result.Result Unit Error)
  := do
  let i := Slice.len accounts
  if i != expected
  then
    let i1 := Slice.len accounts
    if i1 < expected
    then
      ok (core.result.Result.Err
        Error.NotEnoughAccountKeys)
    else
      ok (core.result.Result.Err
        Error.InvalidArgument)
  else ok (core.result.Result.Ok ())

/-- [aspis_pool::processor::require_payer_and_system_program]:
    Source: 'programs/aspis-pool/src/processor.rs', lines 211:0-231:1 -/
def processor.require_payer_and_system_program
  (payer : Account)
  (system_program_account : Account) :
  Result (core.result.Result Unit Error)
  := do
  if payer.is_signer
  then
    if payer.is_writable
    then
      if payer.executable
      then
        let pe ←
          ok invalidPayer
        ok (core.result.Result.Err pe)
      else
        let p ← ok systemId
        let b ←
          Hiq_PoolSource.keyNe payer.owner p
        if b
        then
          let pe ←
            ok invalidPayer
          ok (core.result.Result.Err pe)
        else
          let b1 ←
            Hiq_PoolSource.keyNe
              system_program_account.key p
          if b1
          then
            let pe ←
              ok invalidSystem
            ok (core.result.Result.Err pe)
          else
            let p1 ← ok nativeLoaderId
            let b2 ←
              Hiq_PoolSource.keyNe
                system_program_account.owner p1
            if b2
            then
              let pe ←
                ok invalidSystem
              ok (core.result.Result.Err pe)
            else
              if system_program_account.executable
              then
                if system_program_account.is_signer
                then
                  let pe ←
                    ok invalidSystem
                  ok (core.result.Result.Err pe)
                else
                  if system_program_account.is_writable
                  then
                    let pe ←
                      ok invalidSystem
                    ok (core.result.Result.Err pe)
                  else ok (core.result.Result.Ok ())
              else
                let pe ←
                  ok invalidSystem
                ok (core.result.Result.Err pe)
    else
      let pe ←
        ok invalidPayer
      ok (core.result.Result.Err pe)
  else
    let pe ←
      ok invalidPayer
    ok (core.result.Result.Err pe)

#print axioms pair_forest.require_exact_account_count
#print axioms processor.require_payer_and_system_program
end AspisR1.PoolS2_PrefixSource
end
