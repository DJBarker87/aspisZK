import NNH_MRegistryV2Head
import NNH_MRegistryDataValue
import NNH_MRegistryScalarOps
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryV2HeadTransport
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey)
 (F : RSL.RegistryV2 → Except RSL.ProgramError Unit)
 (hc : ∀ reg, outer (reply id)
   (NNH_MRegistryV2Head.decoded (NNH_MRegistryOps.install base D env) v p m s r e t rp (unkey RSL.LOADER_ID) reg) =
   ok (F (registryV2 reg))) :
 outer (reply id) (NND_RegistryBranches.v2 (NNH_MRegistryOps.install base D env) v p m s r e t rp) =
 ok (ebind (account r).bytes (fun b =>
  ebind (option ((NNH_MRegistryLibrary.install L).decodeRegistryV2 b) .invalidAccountData) F)) := by
 rw [NNH_MRegistryV2Head.source]
 unfold NNH_MRegistryV2Head.run
 rw [NNH_MRegistryScalarOps.loader]
 simp only [bind_tc_ok]
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
   change _ = ok (ebind (option (NNH_MV2DecoderValues.registry (bytes buf.deref)) .invalidAccountData) F)
   rw [NNH_MV2DecoderValues.registry_bytes]
   change _ = ok (ebind (option (NNH_MV1DecoderValues.asOption registryV2
    (NNH_MRegistryReplies.registry2 buf.deref)) .invalidAccountData) F)
   have dec : (NNH_MRegistryOps.install base D env).op33 buf.deref =
    ok (NNH_MRegistryReplies.registry2 buf.deref) := NNH_MRegistryReplies.registry2_eq _
   rw [dec]
   cases hd : NNH_MRegistryReplies.registry2 buf.deref with
   | Err err => rfl
   | Ok reg =>
     change outer (reply id)
      (NNH_MRegistryV2Head.decoded (NNH_MRegistryOps.install base D env) v p m s r e t rp (unkey RSL.LOADER_ID) reg) =
      ok (F (registryV2 reg))
     exact hc reg

#print axioms value
end NNH_MRegistryV2HeadTransport
end
