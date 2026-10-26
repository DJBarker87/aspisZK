import PoolL_MarkerControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_MarkerAccepted
open Aeneas Aeneas.Std Result PoolL_MarkerSource PoolL_MarkerControl
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _
theorem accepted (a : Account) :
    PoolL_marker_header a = ok (.Ok ()) ↔ a.executable = false ∧ a.is_signer = false ∧ a.is_writable = true := by
  rw [control]
  cases he : a.executable <;> cases hs : a.is_signer <;> cases hw : a.is_writable <;> simp
#print axioms accepted
end AspisR1.PoolL_MarkerAccepted
end
