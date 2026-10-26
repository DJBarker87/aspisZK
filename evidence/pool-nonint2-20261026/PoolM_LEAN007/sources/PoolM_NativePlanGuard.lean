import Hiq_PoolSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolM_NativePlanGuard
open Aeneas Aeneas.Std Result
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Error := AdapterRw.solana_program_error.ProgramError

/-- Native AENEAS003 guard body installed on the canonical SDK metadata
carrier. Only external Pubkey inequality and AccountInfo.data_len are bound.
The data_len Result is retained, including failure/divergence; no borrow
success is assumed here. The native SDK cut must supply this same result. -/
def run (a : Account) (id : Key) (size : Usize) (readLength : Result Usize) :
    Result (core.result.Result Unit Error) := do
  let different ← Hiq_PoolSource.keyNe a.owner id
  if different then ok (.Err .InvalidAccountData) else
    if a.executable then ok (.Err .InvalidAccountData) else
      if a.is_signer then ok (.Err .InvalidAccountData) else
        if a.is_writable then do
          let actual ← readLength
          if actual != size then ok (.Err .InvalidAccountData) else ok (.Ok ())
        else ok (.Err .InvalidAccountData)

theorem key_ne (x y : Key) : Hiq_PoolSource.keyNe x y = ok (decide (x ≠ y)) := by
  classical
  simp [Hiq_PoolSource.keyNe,Hist_Authority.keyEq]

theorem owner_error (a : Account) (id : Key) (size : Usize)
    (readLength : Result Usize) (h : a.owner ≠ id) :
    run a id size readLength = ok (.Err .InvalidAccountData) := by
  simp [run,key_ne,h]

/-- All earlier metadata errors dominate the opaque SDK length operation. -/
theorem metadata_error (a : Account) (id : Key) (size : Usize)
    (readLength : Result Usize)
    (h : a.owner ≠ id ∨ a.executable = true ∨ a.is_signer = true ∨ a.is_writable = false) :
    run a id size readLength = ok (.Err .InvalidAccountData) := by
  classical
  by_cases owner : a.owner = id
  · cases he : a.executable <;> cases hs : a.is_signer <;> cases hw : a.is_writable <;>
      simp_all [run,key_ne]
  · exact owner_error a id size readLength owner

theorem size_error (a : Account) (id : Key) (size actual : Usize)
    (wrong : actual ≠ size) :
    run a id size (ok actual) = ok (.Err .InvalidAccountData) := by
  classical
  by_cases owner : a.owner = id
  · cases he : a.executable <;> cases hs : a.is_signer <;> cases hw : a.is_writable <;>
      simp [run,key_ne,owner,he,hs,hw,wrong]
  · exact owner_error a id size (ok actual) owner

/-- Accepted native guard inversion, with the actual length cut retained. -/
theorem accepted (a : Account) (id : Key) (size : Usize) (readLength : Result Usize) :
    run a id size readLength = ok (.Ok ()) ↔
    a.owner = id ∧ a.executable = false ∧ a.is_signer = false ∧
      a.is_writable = true ∧ readLength = ok size := by
  classical
  by_cases owner : a.owner = id
  · cases he : a.executable <;> cases hs : a.is_signer <;> cases hw : a.is_writable <;>
      cases readLength <;> simp [run,key_ne,owner,he,hs,hw] <;> scalar_tac
  · simp [owner_error a id size readLength owner,owner]

#print axioms key_ne
#print axioms owner_error
#print axioms metadata_error
#print axioms size_error
#print axioms accepted
end AspisR1.PoolM_NativePlanGuard
end
