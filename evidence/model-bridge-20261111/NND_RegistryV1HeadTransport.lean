import NND_RegistryV1Head
import NND_RegistryDataValue
set_option autoImplicit false
noncomputable section
namespace NND_RegistryV1HeadTransport
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey)
 (F : RSL.RegistryV1 → Except RSL.ProgramError Unit)
 (hc : ∀ reg, outer (reply id)
   (NND_RegistryV1Head.decoded (NND_RegistryOps.install base D env) v p m s r e t rp reg) =
   ok (F (registryV1 reg))) :
 outer (reply id) (NND_RegistryBranches.v1 (NND_RegistryOps.install base D env) v p m s r e t rp) =
 ok (ebind (account r).data (fun b =>
  ebind (option ((NND_RegistryLibrary.install L).decodeRegistryV1 b) .invalidAccountData) F)) := by
 rw [NND_RegistryV1Head.source]
 unfold NND_RegistryV1Head.run
 apply NND_RegistryDataValue.bind_value
 intro b
 change outer (reply id) (NND_FormatControl.thenCall (NJQ_Canonical.registry b)
  (NND_RegistryV1Head.decoded (NND_RegistryOps.install base D env) v p m s r e t rp)) = _
 rw [NND_RegistryReplies.registry1_eq]
 have h := NND_FormatControl.transport (NND_RegistryReplies.registry1 b)
  (NND_RegistryV1Head.decoded (NND_RegistryOps.install base D env) v p m s r e t rp)
  registryV1 id F hc
 simpa only [NND_RegistryLibrary.install,NND_V1DecoderValues.registry_bytes,NND_RegistryReplies.registry1] using h

#print axioms value
end NND_RegistryV1HeadTransport
end
