import NND_Entry2Decode
import NND_RegistryDataValue
set_option autoImplicit false
noncomputable section
namespace NND_Entry2DecodeTransport
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (F : RSL.EntryV2 → Except RSL.ProgramError Unit)
 (hc : ∀ entry, outer (reply id)
   (NND_Entry2Pda.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID) entry) =
   ok (F (entryV2 entry))) :
 outer (reply id) (NND_Entry2Decode.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID)) =
 ok (ebind (account e).data (fun b =>
  ebind (option ((NND_RegistryLibrary.install L).decodeEntryV2 b) .invalidAccountData) F)) := by
 unfold NND_Entry2Decode.run
 rw [NND_RegistryStd.data]
 cases hb : e.bytes with
 | Err err =>
   simp only [bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
   have hr : (account e).data = .error (error err) := by simp [account,RSL.OwnedAccount.data,hb,reply]
   rw [hr]
   rfl
 | Ok buf =>
   simp only [bind_tc_ok,Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch]
   have hr : (account e).data = .ok (bytes buf.deref) := by
    simp [account,RSL.OwnedAccount.data,hb,reply,bytes,alloc.vec.Vec.deref]
   rw [hr]
   simp only [ebind]
   change _ = ok (ebind (option (NND_V2DecoderValues.entry (bytes buf.deref)) .invalidAccountData) F)
   rw [NND_V2DecoderValues.entry_bytes]
   change _ = ok (ebind (option (NND_V1DecoderValues.asOption entryV2
    (NND_RegistryReplies.entry2 buf.deref)) .invalidAccountData) F)
   have dec : (NND_RegistryOps.install base D env).op34 buf.deref =
    ok (NND_RegistryReplies.entry2 buf.deref) := NND_RegistryReplies.entry2_eq _
   rw [dec]
   cases hd : NND_RegistryReplies.entry2 buf.deref with
   | Err err => rfl
   | Ok entry =>
     change outer (reply id)
      (NND_Entry2Pda.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID) entry) =
      ok (F (entryV2 entry))
     exact hc entry

#print axioms value
end NND_Entry2DecodeTransport
end
