import NNH_MEntry2Decode
import NNH_MRegistryDataValue
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry2DecodeTransport
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (F : RSL.EntryV2 → Except RSL.ProgramError Unit)
 (hc : ∀ entry, outer (reply id)
   (NNH_MEntry2Pda.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID) entry) =
   ok (F (entryV2 entry))) :
 outer (reply id) (NNH_MEntry2Decode.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID)) =
 ok (ebind (account e).bytes (fun b =>
  ebind (option ((NNH_MRegistryLibrary.install L).decodeEntryV2 b) .invalidAccountData) F)) := by
 unfold NNH_MEntry2Decode.run
 rw [NNH_MRegistryStd.data]
 cases hb : e.bytes with
 | Err err =>
   simp only [bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
   have hr : (account e).bytes = .error (error err) := by simp [account,hb,reply]
   rw [hr]
   rfl
 | Ok buf =>
   simp only [bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
   have hr : (account e).bytes = .ok (bytes buf.deref) := by
    simp [account,hb,reply,bytes,alloc.vec.Vec.deref]
   rw [hr]
   simp only [ebind]
   change _ = ok (ebind (option (NNH_MV2DecoderValues.entry (bytes buf.deref)) .invalidAccountData) F)
   rw [NNH_MV2DecoderValues.entry_bytes]
   change _ = ok (ebind (option (NNH_MV1DecoderValues.asOption entryV2
    (NNH_MRegistryReplies.entry2 buf.deref)) .invalidAccountData) F)
   have dec : (NNH_MRegistryOps.install base D env).op34 buf.deref =
    ok (NNH_MRegistryReplies.entry2 buf.deref) := NNH_MRegistryReplies.entry2_eq _
   rw [dec]
   cases hd : NNH_MRegistryReplies.entry2 buf.deref with
   | Err err => rfl
   | Ok entry =>
     change outer (reply id)
      (NNH_MEntry2Pda.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID) entry) =
      ok (F (entryV2 entry))
     exact hc entry

#print axioms value
end NNH_MEntry2DecodeTransport
end
