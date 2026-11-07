import NNH_RegistryConfig
import NND_Registry
set_option autoImplicit false
noncomputable section
namespace NNH_RegistrySdkCall
open Aeneas Aeneas.Std AspisR1 AdapterRw
/-- Equality only for the reached registry call. No dictionary-wide
compatibility assumption is introduced; residual host components are unused. -/
theorem same {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (D : RSL.DeployedIds) (env : RSL.Env) (err : E) (r : NP6_StdModel.Reservation)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 r1_pool_adapter.owned.authenticate_invariant_release_registry
  (NNH_RegistryConfig.sdk missing D env err r) v p m s reg ent t =
 r1_pool_adapter.owned.authenticate_invariant_release_registry
  (NNH_MRegistryOps.install (NNH_RegistryConfig.sdk missing D env err r) D env) v p m s reg ent t := by
 rfl
#print axioms same
end NNH_RegistrySdkCall
