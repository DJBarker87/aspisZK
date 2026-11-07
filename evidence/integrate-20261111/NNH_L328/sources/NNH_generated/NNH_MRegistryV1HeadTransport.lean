import NNH_MRegistryV1Head
import NNH_MRegistryDataValue
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryV1HeadTransport
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey)
 (F : RSL.RegistryV1 → Except RSL.ProgramError Unit)
 (hc : ∀ reg, outer (reply id)
   (NNH_MRegistryV1Head.decoded (NNH_MRegistryOps.install base D env) v p m s r e t rp reg) =
   ok (F (registryV1 reg))) :
 outer (reply id) (NND_RegistryBranches.v1 (NNH_MRegistryOps.install base D env) v p m s r e t rp) =
 ok (ebind (account r).bytes (fun b =>
  ebind (option ((NNH_MRegistryLibrary.install L).decodeRegistryV1 b) .invalidAccountData) F)) := by
 rw [NNH_MRegistryV1Head.source]
 unfold NNH_MRegistryV1Head.run
 rw [NNH_MRegistryStd.data]
 cases hb : r.bytes with
 | Err err =>
   simp only [bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
   have hr : (account r).bytes = .error (error err) := by simp [account,hb,reply]
   rw [hr]
   rfl
 | Ok buf =>
   simp only [bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
   have hr : (account r).bytes = .ok (bytes buf.deref) := by
    simp [account,hb,reply,bytes,alloc.vec.Vec.deref]
   rw [hr]
   simp only [ebind]
   change _ = ok (ebind (option (NNH_MV1DecoderValues.registry (bytes buf.deref)) .invalidAccountData) F)
   rw [NNH_MV1DecoderValues.registry_bytes]
   change _ = ok (ebind (option (NNH_MV1DecoderValues.asOption registryV1
    (NNH_MRegistryReplies.registry1 buf.deref)) .invalidAccountData) F)
   have dec : (NNH_MRegistryOps.install base D env).op31 buf.deref =
    ok (NNH_MRegistryReplies.registry1 buf.deref) := NNH_MRegistryReplies.registry1_eq _
   rw [dec]
   cases hd : NNH_MRegistryReplies.registry1 buf.deref with
   | Err err => rfl
   | Ok reg =>
     change outer (reply id)
      (NNH_MRegistryV1Head.decoded (NNH_MRegistryOps.install base D env) v p m s r e t rp reg) =
      ok (F (registryV1 reg))
     exact hc reg

#print axioms value
end NNH_MRegistryV1HeadTransport
end
