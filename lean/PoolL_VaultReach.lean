import PoolL_VaultAccepted
set_option autoImplicit false
namespace AspisR1.PoolL_VaultReach
open Aeneas Aeneas.Std Result PoolL_VaultSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
/-- Concrete success of this extracted header; authenticated whole-handler
reachability and checkpoint provenance are separate obligations. -/
theorem reachable (a : Account) (expected : Key) :
    PoolL_vault_header {a with key := expected, executable := false, is_signer := false, is_writable := true} expected = ok (.Ok ()) := by
  apply (PoolL_VaultAccepted.accepted _ _).mpr
  simp
#print axioms reachable
end AspisR1.PoolL_VaultReach
