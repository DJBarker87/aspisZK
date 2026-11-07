import NND_RegistryV2Head
import NND_RegistryDataValue
import NND_RegistryScalarOps
set_option autoImplicit false
noncomputable section
namespace NND_RegistryV2HeadTransport
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey)
 (F : RSL.RegistryV2 → Except RSL.ProgramError Unit)
 (hc : ∀ reg, outer (reply id)
   (NND_RegistryV2Head.decoded (NND_RegistryOps.install base D env) v p m s r e t rp (unkey RSL.LOADER_ID) reg) =
   ok (F (registryV2 reg))) :
 outer (reply id) (NND_RegistryBranches.v2 (NND_RegistryOps.install base D env) v p m s r e t rp) =
 ok (ebind (account r).data (fun b =>
  ebind (option ((NND_RegistryLibrary.install L).decodeRegistryV2 b) .invalidAccountData) F)) := by
 rw [NND_RegistryV2Head.source]
 unfold NND_RegistryV2Head.run
 rw [NND_RegistryScalarOps.loader]
 simp only [bind_tc_ok]
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
   change _ = ok (ebind (option (NND_V2DecoderValues.registry (bytes buf.deref)) .invalidAccountData) F)
   rw [NND_V2DecoderValues.registry_bytes]
   change _ = ok (ebind (option (NND_V1DecoderValues.asOption registryV2
    (NND_RegistryReplies.registry2 buf.deref)) .invalidAccountData) F)
   have dec : (NND_RegistryOps.install base D env).op33 buf.deref =
    ok (NND_RegistryReplies.registry2 buf.deref) := NND_RegistryReplies.registry2_eq _
   rw [dec]
   cases hd : NND_RegistryReplies.registry2 buf.deref with
   | Err err => rfl
   | Ok reg =>
     change outer (reply id)
      (NND_RegistryV2Head.decoded (NND_RegistryOps.install base D env) v p m s r e t rp (unkey RSL.LOADER_ID) reg) =
      ok (F (registryV2 reg))
     exact hc reg

#print axioms value
end NND_RegistryV2HeadTransport
end
