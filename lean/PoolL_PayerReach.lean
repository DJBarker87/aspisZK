import PoolL_PayerAccepted
set_option autoImplicit false
namespace AspisR1.PoolL_PayerReach
open Aeneas Aeneas.Std Result PoolL_AllocateSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey

theorem reachable (payer sys : Account) (system loader : Key) :
    payerSystem system loader
      {payer with owner := system, is_signer := true, is_writable := true, executable := false}
      {sys with key := system, owner := loader, is_signer := false, is_writable := false, executable := true} =
      ok (.Ok ()) := by
  apply (PoolL_PayerAccepted.accepted _ _ _ _).mpr
  simp
#print axioms reachable
end AspisR1.PoolL_PayerReach
