import S2W_D189Interpretation
import S2W_EntryPrivileges

/-! Runtime account interpretation used to instantiate D189. Finite Rust byte
buffers and full metadata are inputs. Snapshots are COMPUTED from these inputs,
with the same admitted-length/deferred-error branches as the Kani-checked
native wrapper. No owned snapshot shape, post-state, or alias-frame is input. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_D189Entry
open Aeneas Aeneas.Std Result S2Trust
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_EntryWriteHistory
open MultiproofConeCanonical AspisV8R19.DuplexFrames
abbrev Owned := AdapterRw.Cuts.Account

structure Record where
  owned : Owned
  lamports : Nat
  rentEpoch : Nat

structure Entry where
  handles : Nat → Nat × Nat
  records : Nat → Record
  buffers : Nat → Slice U8
  base : Nat → Nat
  provenance : Nat → Nat

def Entry.payload (e : Entry) (c : Nat) : Payload :=
  {(source (nativeBytes (e.buffers c))) with
    descriptor := ⟨e.base c,(e.buffers c).val.length,e.provenance c⟩}

def Entry.heap (e : Entry) : Heap (Nat → Record) where
  accounts := e.handles
  ownerLive := fun _ => true
  allocated := fun _ => true
  payload := e.payload
  counter := fun _ => 0
  external := fun _ => 0
  guards := []
  ambient := e.records

/-- Full native metadata is interpreted by cell identity. Duplicate runtime
handles denote the same account record/privileges. Allocator and syscall
state are outside this account-only projection, as permitted by D189/P2-P4. -/
def Entry.metadata (e : Entry) (records : Nat → Record) (a : Nat) : S2LeadInterface.Account :=
  let r := records (e.handles a).1
  {key := bytesOf r.owned.key.val,owner := bytesOf r.owned.owner.val,
   lamports := r.lamports,data := [],signer := r.owned.is_signer,
   writable := r.owned.is_writable,executable := r.owned.executable,rentEpoch := r.rentEpoch}

/-- Selected-cell snapshot contract, lifted to the complete retained buffer.
Under runtime admission borrow cannot fail; malformed length is deferred.
Vec allocation failure is transaction abort, outside the accepted branch. -/
def Entry.snapshot (e : Entry) (a len1 len2 : Nat) : Owned :=
  let bytes := e.buffers (e.handles a).1
  {(e.records (e.handles a).1).owned with
    length := .Ok (Slice.len bytes)
    bytes := if bytes.val.length = len1 ∨ bytes.val.length = len2 then .Ok bytes
      else .Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData}

def Entry.first (e : Entry) : S2W_ExtractionBoundary.Accounts :=
  ⟨[e.snapshot 0 58295 58295,e.snapshot 1 1880 1880,e.snapshot 2 1768 1768],by decide⟩

def Entry.second (e : Entry) (sizes : Nat → Nat × Nat) : S2W_ExtractionBoundary.Accounts :=
  ⟨List.ofFn (fun i : Fin 7 => e.snapshot i.val (sizes i.val).1 (sizes i.val).2),by simp; decide⟩

 theorem first_index (e : Entry) :
    Slice.index_usize e.first 0#usize = ok (e.snapshot 0 58295 58295) ∧
    Slice.index_usize e.first 1#usize = ok (e.snapshot 1 1880 1880) ∧
    Slice.index_usize e.first 2#usize = ok (e.snapshot 2 1768 1768) := by
  rfl

/-- Alias exclusion follows from the ACTUAL source privilege guards, without
assuming distinct keys, distinct data cells, or the accountFrame conclusion. -/
theorem first_disjoint (e : Entry) (ops : AdapterRw.Ops)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e.first data = ok (.Ok saved)) :
    ∀ a, a < 3 → a ≠ 2 → (e.heap.accounts a).1 ≠ (e.heap.accounts 2).1 := by
  obtain ⟨pa,pu,ca,ip,iu,ic,rp,ru,rc⟩ :=
    S2W_EntryPrivileges.accepted_privileges ops program e.first data saved accepted
  have eqp := Result.ok.inj (ip.symm.trans (first_index e).1)
  have equ := Result.ok.inj (iu.symm.trans (first_index e).2.1)
  have eqc := Result.ok.inj (ic.symm.trans (first_index e).2.2)
  subst pa; subst pu; subst ca
  change (e.records (e.handles 0).1).owned.is_writable = false at rp
  change (e.records (e.handles 1).1).owned.is_writable = false at ru
  change (e.records (e.handles 2).1).owned.is_writable = true at rc
  intro a within different same
  change (e.handles a).1 = (e.handles 2).1 at same
  have cases : a = 0 ∨ a = 1 := by omega
  rcases cases with h | h
  · subst a; rw [same,rc] at rp; cases rp
  · subst a; rw [same,rc] at ru; cases ru

/-- The destination length is derived from the SAME accepted checkpoint read
and the native wrapper's deferred-length branch; no entrySize premise. -/
theorem checkpoint_size (e : Entry) (ops : AdapterRw.Ops)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e.first data = ok (.Ok saved)) :
    (e.heap.payload (e.heap.accounts 2).1).descriptor.length = 1768 := by
  obtain ⟨ca,bytes,ic,read,_⟩ := AdapterRw.Cuts.stage1_checkpoint_length ops program e.first data saved accepted
  have eqc := Result.ok.inj (ic.symm.trans (first_index e).2.2)
  subst ca
  obtain ⟨copied,stored,_⟩ := S2W.SnapshotJoin.data_success ops (e.snapshot 2 1768 1768) bytes read
  change (if (e.buffers (e.handles 2).1).val.length = 1768 ∨
      (e.buffers (e.handles 2).1).val.length = 1768 then _ else _) = .Ok copied at stored
  split at stored
  · rename_i size
    exact size.elim id id
  · cases stored

#print axioms first_index
#print axioms first_disjoint
#print axioms checkpoint_size
end AspisR1.S2W_D189Entry
end
