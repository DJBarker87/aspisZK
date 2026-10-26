import PoolL_FreshControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_FreshAccepted
open Aeneas Aeneas.Std Result PoolL_FreshSource PoolL_FreshControl
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _
theorem accepted (a : Account) (expected : Key) :
    PoolL_fresh_header a expected = ok (.Ok ()) ↔ a.key = expected ∧ a.executable = false ∧ a.is_signer = false ∧ a.is_writable = true := by
  rw [control]
  by_cases hk : a.key = expected <;> cases he : a.executable <;> cases hs : a.is_signer <;> cases hw : a.is_writable <;> simp [hk]
#print axioms accepted
end AspisR1.PoolL_FreshAccepted
end
