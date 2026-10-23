import S2W_SnapshotFacts
import S2X_SnapshotWrite

/-! Connect the exact extracted snapshot to the owned accepted caller.
The one remaining snapshot-return equality is a wrapper observation, not an
OwnedSnapshotShape/entrySize assumption and not yet reified from a native run. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W.SnapshotJoin
open Aeneas Aeneas.Std Result
open AspisR1.AdapterRw
open AspisR1.S2W.Snapshot

/-- Invert the actual owned data accessor, including the opaque clone failure
paths. A deferred snapshot error cannot masquerade as successful data. -/
theorem data_success (ownedOps : AdapterRw.Ops) (account : OwnedAccount)
    (data : Slice U8)
    (success : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ownedOps account =
      ok (.Ok data)) :
    ∃ bytes : alloc.vec.Vec U8,
      account.bytes = .Ok bytes ∧ alloc.vec.Vec.deref bytes = data := by
  cases stored : account.bytes with
  | Ok bytes =>
    refine ⟨bytes,stored,?_⟩
    simpa only [AdapterRw.r1_pool_adapter.owned.OwnedAccount.data,stored,
      Result.ok.injEq,core.result.Result.Ok.injEq] using success
  | Err error =>
    unfold AdapterRw.r1_pool_adapter.owned.OwnedAccount.data at success
    rw [stored] at success
    exact False.elim (Cuts.error_bind_ne_ok (ownedOps.op35 error) data success)

/-- The previous snapshot-shape hypothesis is derived from the snapshot
execution itself, on the same returned account and successful data read. -/
theorem snapshot_shape (C : Carriers) (ops : Ops C) (ownedOps : AdapterRw.Ops)
    (account : AccountInfo C) (length1 length2 : Usize)
    (out : OwnedAccount) (data : Slice U8)
    (returned : snapshot C ops account length1 length2 = ok out)
    (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ownedOps out =
      ok (.Ok data)) : AspisR1.S2X.OwnedSnapshotShape ownedOps out := by
  obtain ⟨bytes,stored,_⟩ := data_success ownedOps out data read
  exact ⟨bytes,stored,(successful_shape C ops account length1 length2 out bytes
    returned stored).1⟩

/-- The SAME checkpoint returned by accepted owned TX1 has1768 bytes, with
neither OwnedSnapshotShape nor entrySize supplied as a premise. Native entry
indexing/SDK interpretation still must supply the displayed snapshot return. -/
theorem accepted_checkpoint_length (C : Carriers) (ops : Ops C)
    (ownedOps : AdapterRw.Ops) (nativeCheckpoint : AccountInfo C)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Cuts.Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ownedOps program accounts data =
      ok (.Ok checkpoint))
    (at2 : Cuts.Account)
    (selected : Slice.index_usize accounts 2#usize = ok at2)
    (returned : snapshot C ops nativeCheckpoint 1768#usize 1768#usize = ok at2) :
    checkpoint.val.length = 1768 := by
  obtain ⟨account,bytes,index,read,sameLength⟩ :=
    Cuts.stage1_checkpoint_length ownedOps program accounts data checkpoint accepted
  have same : account = at2 := Result.ok.inj (index.symm.trans selected)
  subst account
  obtain ⟨copied,stored,view⟩ := data_success ownedOps at2 bytes read
  have size := checkpoint_entry_size C ops nativeCheckpoint at2 copied returned stored
  have length := congrArg UScalar.val sameLength
  rw [← view] at length
  exact length.trans size

#print axioms data_success
#print axioms snapshot_shape
#print axioms accepted_checkpoint_length
end AspisR1.S2W.SnapshotJoin
end
