import PoolW_ZeroFacts
import Hiq_PoolGuards
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolW_ZeroGuard
open Aeneas Aeneas.Std Result
abbrev Error := AdapterRw.solana_program_error.ProgramError
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey

def invalidFresh : Error := .Custom 1095966773#u32

/-- P6 guard reference. Read errors and interpreter failures are retained.
This does not assert the missing native/reference whole-guard coupling. -/
def run (account : Account) (id : Key) (exact : Nat)
    (read : Result (core.result.Result (Slice U8) Error)) (exempt : Bool) :
    Result (core.result.Result Unit Error) := do
  let admission ← Hiq_PoolSource.history.require_program_account account id true
  match admission with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    let loaded ← read
    match loaded with
    | .Err e => ok (.Err e)
    | .Ok data =>
      if data.val.length != exact then ok (.Err invalidFresh) else do
        let zero ← PoolW_Zero.zero_bytes data
        if !zero || !exempt then ok (.Err invalidFresh) else ok (.Ok ())

theorem metadata_error (a : Account) (id : Key) (exact : Nat)
    (read : Result (core.result.Result (Slice U8) Error)) (exempt : Bool) (e : Error)
    (rejected : Hiq_PoolSource.history.require_program_account a id true = ok (.Err e)) :
    run a id exact read exempt = ok (.Err e) := by
  simp [run,rejected]

theorem read_error (a : Account) (id : Key) (exact : Nat) (exempt : Bool) (e : Error)
    (admitted : Hiq_PoolSource.history.require_program_account a id true = ok (.Ok ())) :
    run a id exact (ok (.Err e)) exempt = ok (.Err e) := by
  simp [run,admitted]

theorem accepted (a : Account) (id : Key) (exact : Nat)
    (data : Slice U8) (exempt : Bool)
    (admitted : Hiq_PoolSource.history.require_program_account a id true = ok (.Ok ())) :
    run a id exact (ok (.Ok data)) exempt = ok (.Ok ()) ↔
      data.val.length = exact ∧ (∀ byte ∈ data.val, byte = 0#u8) ∧ exempt = true := by
  rw [run,admitted]
  classical
  have norm : (∀ byte ∈ data.val, byte.val = 0) ↔ (∀ byte ∈ data.val, byte = 0#u8) := by
    constructor <;> intro h byte member <;> have hb := h byte member <;> scalar_tac
  by_cases size : data.val.length = exact
  · by_cases zero : ∀ byte ∈ data.val, byte.val = 0
    · have actualZero := norm.mp zero
      cases exempt <;> simp [PoolW_ZeroExact.exact,size,zero,actualZero]
    · have actualNonzero : ¬ ∀ byte ∈ data.val, byte = 0#u8 := by
        exact fun h => zero (norm.mpr h)
      simp [PoolW_ZeroExact.exact,size,zero,actualNonzero]
  · simp [PoolW_ZeroExact.exact,size]

#print axioms metadata_error
#print axioms read_error
#print axioms accepted
end AspisR1.PoolW_ZeroGuard
end
