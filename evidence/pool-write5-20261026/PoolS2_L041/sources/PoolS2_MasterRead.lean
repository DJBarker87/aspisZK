import PoolS2_PdaMaster
import Hiq_PoolGuards
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_MasterRead
open Aeneas Aeneas.Std Result PoolS2_PdaSource
abbrev Account := AdapterRw.Cuts.Account
abbrev ProgramError := AdapterRw.solana_program_error.ProgramError
abbrev FormatError := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
abbrev Decode := Slice U8 → Result (core.result.Result Master FormatError)
def invalidType : ProgramError := .Custom 1095966721#u32
def invalidAddress : ProgramError := .Custom 1095966729#u32

/-- Owned VALUE/ERROR reference of F430–450, not the failed native extraction.
`bytes` must mean the raw SDK read outcome, with no deferred length filter.
No Box, typed SDK guard, allocator, cleanup or native/query interpretation is
supplied here. The strict decoder is the real named child function parameter;
its successful call and PDA check are conclusions of acceptance below. -/
def run (decode : Decode) (pda : Ops) (program : Key) (account : Account) (writable : Bool) :
    Result (core.result.Result Master ProgramError) := by
  classical
  exact do
    let metadata ← Hiq_PoolSource.history.require_program_account account program writable
    match metadata with
    | .Err e => ok (.Err e)
    | .Ok _ =>
      if account.is_signer then ok (.Err ProgramError.InvalidAccountData)
      else
        match account.bytes with
        | .Err e => ok (.Err e)
        | .Ok bytes =>
          let decoded ← decode bytes.deref
          match decoded with
          | .Err _ => ok (.Err invalidType)
          | .Ok master =>
            let address ← pair_forest.master_address_matches pda program master account.key
            if !address || decide (master.identity.pool ≠ account.key)
            then ok (.Err invalidAddress)
            else ok (.Ok master)

#print axioms run
end AspisR1.PoolS2_MasterRead
end
