import NNH_MEntry1Decode
import NNH_MRegistryDataValue
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry1DecodeTransport
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey)
 (F : RSL.EntryV1 → Except RSL.ProgramError Unit)
 (hc : ∀ entry, outer (reply id)
   (NNH_MEntry1Pda.run (NNH_MRegistryOps.install base D env) v m.key rp e t entry) =
   ok (F (entryV1 entry))) :
 outer (reply id) (NNH_MEntry1Decode.run (NNH_MRegistryOps.install base D env) v m.key rp e t) =
 ok (ebind (account e).bytes (fun b =>
  ebind (option ((NNH_MRegistryLibrary.install L).decodeEntryV1 b) .invalidAccountData) F)) := by
 unfold NNH_MEntry1Decode.run
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
   change _ = ok (ebind (option (NNH_MV1DecoderValues.entry (bytes buf.deref)) .invalidAccountData) F)
   rw [NNH_MV1DecoderValues.entry_bytes]
   change _ = ok (ebind (option (NNH_MV1DecoderValues.asOption entryV1
    (NNH_MRegistryReplies.entry1 buf.deref)) .invalidAccountData) F)
   have dec : (NNH_MRegistryOps.install base D env).op32 buf.deref =
    ok (NNH_MRegistryReplies.entry1 buf.deref) := NNH_MRegistryReplies.entry1_eq _
   rw [dec]
   cases hd : NNH_MRegistryReplies.entry1 buf.deref with
   | Err err => rfl
   | Ok entry =>
     change outer (reply id)
      (NNH_MEntry1Pda.run (NNH_MRegistryOps.install base D env) v m.key rp e t entry) =
      ok (F (entryV1 entry))
     exact hc entry

#print axioms value
end NNH_MEntry1DecodeTransport
end
