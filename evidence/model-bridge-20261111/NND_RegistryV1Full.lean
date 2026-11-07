import NND_Registry1DecodedValue
import NND_RegistryV1HeadTransport
import NND_RegistryEval
set_option autoImplicit false
noncomputable section
namespace NND_RegistryV1Full
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id) (NND_RegistryBranches.v1 (NND_RegistryOps.install base D env) v p m s r e t (unkey D.registry)) =
 ok (NND_RegistryEval.v1Value (NND_RegistryLibrary.install L) D (NND_RegistryArgs.args v p m s r e t) env) := by
 apply NND_RegistryV1HeadTransport.value base L D env v p m s r e t (unkey D.registry)
 intro reg
 exact NND_Registry1DecodedValue.value base L D env v p m s r e t reg

#print axioms value
end NND_RegistryV1Full
end
