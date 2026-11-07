import NNH_MRegistryReturned
import NNH_RegistryLibraryMatch
import NNH_RegistrySdkCall
import NNH_EnvUnique
set_option autoImplicit false
noncomputable section
namespace NNH_RegistryModel
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries
/-- Full canonical234 returned-value bridge at the actual deployed SDK
configuration. Unused residual components stay data, never compatibility laws.
This is a model bridge for A2, not a native234 row candidate. -/
theorem returned {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (reserve : NP6_StdModel.Reservation)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (o : RSL.Obs (Except RSL.ProgramError Unit)) (r : Except RSL.ProgramError Unit)
 (law : RSL.TX2_234.Ref L D (NNH_MRegistryArgs.args v p m s reg ent t) env o)
 (ret : o.exit=.ret r) :
 r1_pool_adapter.owned.authenticate_invariant_release_registry
  (NNH_RegistryConfig.sdk missing D env err reserve) v p m s reg ent t =
 .ok (unreply id r) := by
 rw [NNH_RegistrySdkCall.same]
 apply NNH_MRegistryReturned.returned _ L D env v p m s reg ent t o r
 · rw [NNH_RegistryLibraryMatch.installed]
   exact law
 · exact ret

/-- Pointwise use at any represented Env, with the SDK built from the SAME
runtime binders. Rev3 reservation agreement is consumed via uniqueness. -/
theorem represented {E : Type} (missing : IDa_Deployed.Uninstalled E)
 (sha : List RSL.Bytes → RSL.B32) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (reserve : NP6_StdModel.Reservation)
 (env : RSL.Env) (rep : NNH_HostEnv.EnvRep sha pda clock reserve env) (err : E)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (o : RSL.Obs (Except RSL.ProgramError Unit)) (r : Except RSL.ProgramError Unit)
 (law : RSL.TX2_234.Ref L D (NNH_MRegistryArgs.args v p m s reg ent t) env o)
 (ret : o.exit=.ret r) :
 r1_pool_adapter.owned.authenticate_invariant_release_registry
  (NNH_RegistryConfig.sdk missing D (NNH_HostEnv.environment sha pda clock reserve) err reserve)
  v p m s reg ent t=.ok (unreply id r) := by
 have same := NNH_EnvUnique.unique sha pda clock reserve env rep
 subst env
 exact returned missing _ err reserve v p m s reg ent t o r law ret

#print axioms returned
#print axioms represented
end NNH_RegistryModel
