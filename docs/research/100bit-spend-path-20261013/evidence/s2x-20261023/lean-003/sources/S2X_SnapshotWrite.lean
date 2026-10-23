import AdapterRwSdkSnapshots
import AdapterRwLeadInputs

set_option autoImplicit false
namespace AspisR1.S2X
open Aeneas Aeneas.Std Result
open S2Trust AdapterRw AdapterRw.LeadInputs

/-- Successful owned data access is a projection of the SAME stored vector.
No operation in Ops is consulted on this branch. -/
theorem owned_data (ops : AdapterRw.Ops) (account : Cuts.Account)
    (bytes : alloc.vec.Vec U8) (stored : account.bytes = .Ok bytes) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops account =
      ok (.Ok (alloc.vec.Vec.deref bytes)) := by
  simp only [AdapterRw.r1_pool_adapter.owned.OwnedAccount.data, stored]

/-- The pure std full-slice copy preserves all bytes, with no concrete
1768-byte reduction. Native memcpy/allocator interpretation remains P6 work. -/
theorem full_copy (target source : Slice U8)
    (sameLength : target.val.length = source.val.length) :
    core.slice.Slice.copy_from_slice core.marker.CopyU8 target source = ok source := by
  simp [core.slice.Slice.copy_from_slice, sameLength]

/-- An explicit source-boundary condition, NOT SDK trust: successful entry
snapshot data equals the entry allocation and its recorded length. The actual
native to_vec wrapper must establish this condition before using length joins. -/
structure OwnedSnapshotShape (ops : AdapterRw.Ops) (account : Cuts.Account) where
  bytes : alloc.vec.Vec U8
  stored : account.bytes = .Ok bytes
  length : account.length = .Ok (alloc.vec.Vec.len bytes)

/-- The owned caller's accepted return has exactly the entry CP snapshot size.
The only 1768 hypothesis is on the entry snapshot, not the returned checkpoint. -/
theorem accepted_checkpoint_length (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Cuts.Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data =
      ok (.Ok checkpoint))
    (account : Cuts.Account)
    (at2 : Slice.index_usize accounts 2#usize = ok account)
    (snapshot : OwnedSnapshotShape ops account) (entrySize : snapshot.bytes.val.length = 1768) :
    checkpoint.val.length = 1768 := by
  obtain ⟨a,bytes,ha,hd,hl⟩ := Cuts.stage1_checkpoint_length ops program accounts data checkpoint accepted
  have same : a = account := Result.ok.inj (ha.symm.trans at2)
  subst a
  have dataEq := owned_data ops account snapshot.bytes snapshot.stored
  have bytesEq : bytes = alloc.vec.Vec.deref snapshot.bytes :=
    core.result.Result.Ok.inj (Result.ok.inj (hd.symm.trans dataEq))
  rw [bytesEq] at hl
  have lengths := congrArg UScalar.val hl
  have : checkpoint.val.length = snapshot.bytes.val.length := by simpa [alloc.vec.Vec.deref] using lengths
  exact this.trans entrySize

/-- One byte of the actual SDK write is licensed by the existing trust item.
Neither native relatedness nor validity at the write cut is fabricated. -/
theorem sdk_write {W F : Type} (L : Library W F) (trust : S2TrustedSdkBorrow L)
    (w : W) (s : Heap F) (g : Guard) (i : Nat) (v : UInt8)
    (related : L.related w s) (valid : Valid s)
    (guard : lookup s g.token = some g) (exclusive : g.kind = .exclusive)
    (within : i < (s.payload g.cell).descriptor.length) :
    Matches L w (.write g.token i v) (writeAt s g i v, .unit) :=
  (trust.exclusive_deref w s g.token g related valid guard exclusive).2 i v within

/-- The primitive write changes only destination payload contents. In
particular it preserves full ambient metadata and allocation descriptors. -/
theorem sdk_write_frame {F : Type} (s : Heap F) (g : Guard) (i : Nat) (v : UInt8) :
    (writeAt s g i v).ambient = s.ambient ∧
    (writeAt s g i v).accounts = s.accounts ∧
    (writeAt s g i v).counter = s.counter ∧
    (writeAt s g i v).guards = s.guards ∧
    (∀ c, ((writeAt s g i v).payload c).descriptor = (s.payload c).descriptor) ∧
    (∀ c, c ≠ g.cell → (writeAt s g i v).payload c = s.payload c) := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
  · intro c
    by_cases h : c = g.cell <;> simp [writeAt,put,h]
  · intro c h
    simp [writeAt,put,h]

/-- Exact full-account update used by the single checkpoint writer. This
includes key, owner, lamports, flags and rent epoch, not just Boolean metadata. -/
def commitCheckpoint (before : Nat → S2LeadInterface.Account)
    (checkpoint : AspisV8R19.DuplexFrames.Bytes) : Nat → S2LeadInterface.Account :=
  fun a => if a = 2 then {before a with data := checkpoint} else before a

theorem commit_frame (before : Nat → S2LeadInterface.Account)
    (checkpoint : AspisV8R19.DuplexFrames.Bytes) (a : Nat) (other : a ≠ 2) :
    commitCheckpoint before checkpoint a = before a := by
  simp only [commitCheckpoint,if_neg other]

theorem commit_metadata (before : Nat → S2LeadInterface.Account)
    (checkpoint : AspisV8R19.DuplexFrames.Bytes) :
    {commitCheckpoint before checkpoint 2 with data := (before 2).data} = before 2 := by
  simp [commitCheckpoint]

theorem commit_bytes (before : Nat → S2LeadInterface.Account)
    (checkpoint : AspisV8R19.DuplexFrames.Bytes) :
    (commitCheckpoint before checkpoint 2).data = checkpoint := by
  simp [commitCheckpoint]

#print axioms owned_data
#print axioms full_copy
#print axioms accepted_checkpoint_length
#print axioms sdk_write
#print axioms sdk_write_frame
#print axioms commit_frame
#print axioms commit_metadata
#print axioms commit_bytes
end AspisR1.S2X
