import NND_Entry1Decode
import NND_RegistryDataValue
set_option autoImplicit false
noncomputable section
namespace NND_Entry1DecodeTransport
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey)
 (F : RSL.EntryV1 → Except RSL.ProgramError Unit)
 (hc : ∀ entry, outer (reply id)
   (NND_Entry1Pda.run (NND_RegistryOps.install base D env) v m.key rp e t entry) =
   ok (F (entryV1 entry))) :
 outer (reply id) (NND_Entry1Decode.run (NND_RegistryOps.install base D env) v m.key rp e t) =
 ok (ebind (account e).data (fun b =>
  ebind (option ((NND_RegistryLibrary.install L).decodeEntryV1 b) .invalidAccountData) F)) := by
 unfold NND_Entry1Decode.run
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
   change _ = ok (ebind (option (NND_V1DecoderValues.entry (bytes buf.deref)) .invalidAccountData) F)
   rw [NND_V1DecoderValues.entry_bytes]
   change _ = ok (ebind (option (NND_V1DecoderValues.asOption entryV1
    (NND_RegistryReplies.entry1 buf.deref)) .invalidAccountData) F)
   have dec : (NND_RegistryOps.install base D env).op32 buf.deref =
    ok (NND_RegistryReplies.entry1 buf.deref) := NND_RegistryReplies.entry1_eq _
   rw [dec]
   cases hd : NND_RegistryReplies.entry1 buf.deref with
   | Err err => rfl
   | Ok entry =>
     change outer (reply id)
      (NND_Entry1Pda.run (NND_RegistryOps.install base D env) v m.key rp e t entry) =
      ok (F (entryV1 entry))
     exact hc entry

#print axioms value
end NND_Entry1DecodeTransport
end
