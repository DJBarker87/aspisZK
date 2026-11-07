import NND_Entry2DecodeTransport
import NND_Entry2PdaValue
set_option autoImplicit false
noncomputable section
namespace NND_Entry2DecodedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

def tail := NND_Entry2PdaValue.tail

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id) (NND_Entry2Decode.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID)) =
 ok (ebind (account e).data (fun b =>
  ebind (option ((NND_RegistryLibrary.install L).decodeEntryV2 b) .invalidAccountData)
   (tail env D (NND_RegistryArgs.args v p m s r e t)))) := by
 apply NND_Entry2DecodeTransport.value base L D env v p m s r e t
 intro entry
 exact NND_Entry2PdaValue.value base D env v p m s r e t entry

#print axioms value
end NND_Entry2DecodedValue
end
