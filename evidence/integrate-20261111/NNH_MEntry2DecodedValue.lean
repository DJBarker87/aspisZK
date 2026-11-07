import NNH_MEntry2DecodeTransport
import NNH_MEntry2PdaValue
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry2DecodedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

def tail := NNH_MEntry2PdaValue.tail

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id) (NNH_MEntry2Decode.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID)) =
 ok (ebind (account e).bytes (fun b =>
  ebind (option ((NNH_MRegistryLibrary.install L).decodeEntryV2 b) .invalidAccountData)
   (tail env D (NNH_MRegistryArgs.args v p m s r e t)))) := by
 apply NNH_MEntry2DecodeTransport.value base L D env v p m s r e t
 intro entry
 exact NNH_MEntry2PdaValue.value base D env v p m s r e t entry

#print axioms value
end NNH_MEntry2DecodedValue
end
