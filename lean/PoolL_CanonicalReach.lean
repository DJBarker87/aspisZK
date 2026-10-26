import PoolL_CanonicalAccepted
set_option autoImplicit false
namespace AspisR1.PoolL_CanonicalReach
open Aeneas Aeneas.Std Result PoolL_CanonicalSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
/-- Concrete success of this extracted header; authenticated whole-handler
reachability and checkpoint provenance are separate obligations. -/
theorem reachable (a : Account) (id : Key) :
    PoolL_canonical_header {a with owner := id, executable := false, is_signer := false, is_writable := true} id = ok (.Ok ()) := by
  apply (PoolL_CanonicalAccepted.accepted _ _).mpr
  simp
#print axioms reachable
end AspisR1.PoolL_CanonicalReach
