import NNH_Tx2ModelSlots
import NNH_RegistryCallCongr
import NNH_MRegistryReturned
import NNH_RegistryLibraryMatch
set_option autoImplicit false
noncomputable section
namespace NNH_Tx2RegistryPort
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem same (base : Ops) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 r1_pool_adapter.owned.authenticate_invariant_release_registry (NNH_Tx2ModelSlots.install base env) v p m s reg ent t =
 r1_pool_adapter.owned.authenticate_invariant_release_registry
  (NNH_MRegistryOps.install (NNH_Tx2ModelSlots.install base env) D env) v p m s reg ent t := by
 apply NNH_RegistryCallCongr.same <;> rfl

theorem value (base : Ops) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 r1_pool_adapter.owned.authenticate_invariant_release_registry (NNH_Tx2ModelSlots.install base env) v p m s reg ent t =
 .ok (unreply id (NNH_RegistryEval.value L D (NNH_MRegistryArgs.args v p m s reg ent t) env)) := by
 rw [same,NNH_MRegistryReturned.value _ L D env v p m s reg ent t,NNH_RegistryLibraryMatch.installed]
#print axioms same
#print axioms value
end NNH_Tx2RegistryPort
