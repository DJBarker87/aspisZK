import PoolL_MarkerAccepted
set_option autoImplicit false
namespace AspisR1.PoolL_MarkerReach
open Aeneas Aeneas.Std Result PoolL_MarkerSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
/-- Concrete success of this extracted header; authenticated whole-handler
reachability and checkpoint provenance are separate obligations. -/
theorem reachable (a : Account) :
    PoolL_marker_header {a with executable := false, is_signer := false, is_writable := true} = ok (.Ok ()) := by
  apply (PoolL_MarkerAccepted.accepted _).mpr
  simp
#print axioms reachable
end AspisR1.PoolL_MarkerReach
