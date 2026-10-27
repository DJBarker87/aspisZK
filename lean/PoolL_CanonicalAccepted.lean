import PoolL_CanonicalControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_CanonicalAccepted
open Aeneas Aeneas.Std Result PoolL_CanonicalSource PoolL_CanonicalControl
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _
theorem accepted (a : Account) (id : Key) :
    PoolL_canonical_header a id = ok (.Ok ()) ↔ a.owner = id ∧ a.executable = false ∧ a.is_writable = true ∧ a.is_signer = false := by
  rw [control]
  by_cases ho : a.owner = id <;> cases he : a.executable <;> cases hw : a.is_writable <;> cases hs : a.is_signer <;> simp [ho]
#print axioms accepted
end AspisR1.PoolL_CanonicalAccepted
end
