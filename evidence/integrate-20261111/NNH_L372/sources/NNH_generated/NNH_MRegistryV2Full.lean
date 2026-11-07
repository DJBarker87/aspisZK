import NNH_MRegistry2DecodedValue
import NNH_MRegistryV2HeadTransport
import NNH_RegistryEval
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryV2Full
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id) (NND_RegistryBranches.v2 (NNH_MRegistryOps.install base D env) v p m s r e t (unkey D.registry)) =
 ok (NNH_RegistryEval.immutableValue (NNH_MRegistryLibrary.install L) D (NNH_MRegistryArgs.args v p m s r e t) env) := by
 apply NNH_MRegistryV2HeadTransport.value base L D env v p m s r e t (unkey D.registry)
 intro reg
 exact NNH_MRegistry2DecodedValue.value base L D env v p m s r e t reg

#print axioms value
end NNH_MRegistryV2Full
end
