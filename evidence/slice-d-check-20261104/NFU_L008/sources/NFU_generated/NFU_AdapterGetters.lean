import AdapterRwModel
import NFQ_Readonly
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFU_AdapterGetters
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev PE := AdapterRw.solana_program_error.ProgramError

theorem key (a : Account) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.key a = ok a.key := by rfl

theorem owner (a : Account) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner a = ok a.owner := by rfl

/-- The complete Result of the frozen caller, with the CLOSED NFQ callee. -/
theorem readonly (a : Account) :
    AdapterRw.r1_pool_adapter.owned.require_readonly_buffer a =
      (do let admitted ← NFQ_ScanReference.readonly_buffer_ref
            a.is_signer a.is_writable a.executable
          ok (if admitted then core.result.Result.Ok () else
            .Err PE.InvalidAccountData)) := by
  exact (NFQ_Readonly.reference a.is_signer a.is_writable a.executable).symm

/-- Only these three metadata fields are read; deferred SDK errors and buffers
remain arbitrary, not additional admissibility assumptions. -/
theorem readonly_frame (a b : Account)
    (s : a.is_signer = b.is_signer) (w : a.is_writable = b.is_writable)
    (e : a.executable = b.executable) :
    AdapterRw.r1_pool_adapter.owned.require_readonly_buffer a =
      AdapterRw.r1_pool_adapter.owned.require_readonly_buffer b := by
  simp only [AdapterRw.r1_pool_adapter.owned.require_readonly_buffer, s, w, e]

theorem key_frame (a b : Account) (same : a.key = b.key) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.key a =
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.key b := by
  rw [key, key, same]

theorem owner_frame (a b : Account) (same : a.owner = b.owner) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner a =
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner b := by
  rw [owner, owner, same]
#print axioms key
#print axioms owner
#print axioms readonly
#print axioms readonly_frame
#print axioms key_frame
#print axioms owner_frame
end NFU_AdapterGetters
