import NMX_R3_RegistryEmitted
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryEmittedLink
open Aeneas Aeneas.Std AdapterRw
theorem source (ops : Ops) (v p : solana_pubkey.Pubkey)
 (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 NMX_R3_RegistryEmitted.body ops v p m s r e t =
 r1_pool_adapter.owned.authenticate_invariant_release_registry ops v p m s r e t := by
 rfl
#print axioms source
end NMX_R3_RegistryEmittedLink
end
