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
 rw [NND_RegistryStd.data]
 cases hb : r.bytes with
 | Err err =>
   simp only [bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
   have hr : (account r).data = .error (error err) := by simp [account,RSL.OwnedAccount.data,hb,reply]
   rw [hr]
   rfl
 | Ok buf =>
   simp only [bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
   have hr : (account r).data = .ok (bytes buf.deref) := by
    simp [account,RSL.OwnedAccount.data,hb,reply,bytes,alloc.vec.Vec.deref]
   rw [hr]
   simp only [ebind]
   change _ = ok (ebind (option (NND_V1DecoderValues.registry (bytes buf.deref)) .invalidAccountData) F)
   rw [NND_V1DecoderValues.registry_bytes]
   change _ = ok (ebind (option (NND_V1DecoderValues.asOption registryV1
    (NND_RegistryReplies.registry1 buf.deref)) .invalidAccountData) F)
   have dec : (NND_RegistryOps.install base D env).op31 buf.deref =
    ok (NND_RegistryReplies.registry1 buf.deref) := NND_RegistryReplies.registry1_eq _
   rw [dec]
   cases hd : NND_RegistryReplies.registry1 buf.deref with
   | Err err => rfl
   | Ok reg =>
     change outer (reply id)
      (NND_RegistryV1Head.decoded (NND_RegistryOps.install base D env) v p m s r e t rp reg) =
      ok (F (registryV1 reg))
     exact hc reg

#print axioms value
end NND_RegistryV1HeadTransport
end
