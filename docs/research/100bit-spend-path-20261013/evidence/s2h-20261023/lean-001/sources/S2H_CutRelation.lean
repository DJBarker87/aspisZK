import S2E_Execution
import S2TrustedSdkBorrow

/-! A full-allocation candidate relation. It is intentionally NOT an instance
of a native Library. In particular `Valid`, initial relatedness, metadata and
allocator interpretation must be established from the runtime, not acceptance.
No child callback is given a state frame by this definition. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2H
open S2Trust
open S2E_Reference.S2E_Reference

/-- Complete non-payload state. Oracle history includes rejected queries,
duplicates, syscall and allocation events in order. -/
structure World (Child Alloc Event : Type) where
  accounts : alloc.vec.Vec OwnedAccount
  lamports : alloc.vec.Vec OwnedLamportsCell
  strong : Nat → Usize
  weak : Nat → Usize
  child : Child
  allocator : Alloc
  history : List Event

/-- Abstract allocation identities, independent of raw addresses. Every owned
slot has its original cell and descriptor; aliases are expressed by slot reuse.
Account keys being distinct is never used as a cell-disjointness premise. -/
structure AllocationMap where
  dataCell : Nat → Nat
  lamportsCell : Nat → Nat
  handle : Nat → Nat
  descriptor : Nat → Descriptor
  dataInjective : Function.Injective dataCell
  lamportsInjective : Function.Injective lamportsCell
  handleInjective : Function.Injective handle

/-- ALL original allocations, not only selected proof/public bytes. The native
state index is fixed before execution; the record contains no accepted run. -/
structure Originals (W Child Alloc Event : Type) where
  native : W
  heap : Heap (World Child Alloc Event)
  input : S2E.Original (World Child Alloc Event)
  allocations : AllocationMap

/-- Exact full heap representation, including Rc metadata and lamports. No
slice hashing, bounded-coordinate approximation or equal-length surrogate. -/
structure HeapImage {Child Alloc Event : Type} (m : AllocationMap)
    (h : Heap (World Child Alloc Event)) (sdk : SDK) : Prop where
  accounts : h.ambient.accounts = sdk.accounts
  lamports : h.ambient.lamports = sdk.lamports_cells
  handles : ∀ i account, sdk.accounts.val[i]? = some account →
    h.accounts (m.handle i) =
      (m.dataCell account.data_slot.val,m.lamportsCell account.lamports_slot.val)
  data : ∀ slot cell, sdk.data_cells.val[slot]? = some cell →
    h.allocated (m.dataCell slot) = true ∧
    (h.payload (m.dataCell slot)).descriptor = m.descriptor slot ∧
    (m.descriptor slot).length = cell.bytes.val.length ∧
    h.counter (m.dataCell slot) = cell.borrowed.val ∧
    h.ambient.strong (m.dataCell slot) = cell.strong ∧
    h.ambient.weak (m.dataCell slot) = cell.weak ∧
    ∀ i byte, cell.bytes.val[i]? = some byte →
      (h.payload (m.dataCell slot)).contents i = UInt8.ofNat byte.val
  slots : ∀ i account, sdk.accounts.val[i]? = some account →
    account.data_slot.val < sdk.data_cells.val.length ∧
    account.lamports_slot.val < sdk.lamports_cells.val.length

/-- Live token bindings are independent of the counter-only S2E LiveGuards.
In stage1 CP/public/proof use indices 2/1/0; in stage2 proof/CP use 0/6.
Moves change the owner in Guard; they never fabricate a token from words. -/
structure TokenBinding where
  accountIndex : Nat
  token : Nat
  owner : Nat
  kind : Kind

structure OwnedCut (Child Alloc Event : Type) where
  sdk : SDK
  state : World Child Alloc Event
  heap : Heap (World Child Alloc Event)
  tokens : List TokenBinding
  program : Array U8 32#usize
  instruction : Slice U8

structure CutRelated {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event))
    (o : Originals W Child Alloc Event) (native : W)
    (owned : OwnedCut Child Alloc Event) : Prop where
  nativeHeap : L.related native owned.heap
  valid : Valid owned.heap
  image : HeapImage o.allocations owned.heap owned.sdk
  ambient : owned.heap.ambient = owned.state
  program : owned.program = o.input.program
  instruction : owned.instruction = o.input.data
  tokens : ∀ binding, binding ∈ owned.tokens →
    ∃ account, owned.sdk.accounts.val[binding.accountIndex]? = some account ∧
      lookup owned.heap binding.token = some
        ⟨binding.token,o.allocations.dataCell account.data_slot.val,
          binding.owner,binding.kind,o.allocations.descriptor account.data_slot.val⟩

/-- Initial snapshot relation is separate, never obtained from final acceptance. -/
structure Admitted {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event))
    (o : Originals W Child Alloc Event) : Prop where
  nativeHeap : L.related o.native o.heap
  valid : Valid o.heap
  image : HeapImage o.allocations o.heap o.input.sdk
  ambient : o.heap.ambient = o.input.state

/-- A reached native Rc dereference identifies the selected data and lamport
cells of the SAME full account record. -/
theorem selected_account {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (trust : S2TrustedSdkBorrow L)
    (o : Originals W Child Alloc Event) (n : W) (r : OwnedCut Child Alloc Event)
    (related : CutRelated L o n r) (i : Nat) (account : OwnedAccount)
    (read : r.sdk.accounts.val[i]? = some account) :
    L.accountData n (o.allocations.handle i) = o.allocations.dataCell account.data_slot.val ∧
    L.accountLamports n (o.allocations.handle i) = o.allocations.lamportsCell account.lamports_slot.val := by
  have fields := trust.account_data_cell n r.heap related.nativeHeap related.valid
    (o.allocations.handle i) (o.allocations.handle i)
  have handles := related.image.handles i account read
  exact ⟨fields.1.trans (congrArg Prod.fst handles),
    fields.2.1.trans (congrArg Prod.snd handles)⟩

/-- All coordinates of the selected ORIGINAL allocation, descriptor/provenance,
Rc counts and signed borrow counter are represented at a current cut. -/
theorem selected_data {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (trust : S2TrustedSdkBorrow L)
    (o : Originals W Child Alloc Event) (n : W) (r : OwnedCut Child Alloc Event)
    (related : CutRelated L o n r) (slot : Nat) (cell : OwnedDataCell)
    (read : r.sdk.data_cells.val[slot]? = some cell) :
    (L.cellPayload n (o.allocations.dataCell slot)).descriptor = o.allocations.descriptor slot ∧
    (o.allocations.descriptor slot).length = cell.bytes.val.length ∧
    L.cellCounter n (o.allocations.dataCell slot) = cell.borrowed.val ∧
    ∀ i byte, cell.bytes.val[i]? = some byte →
      (L.cellPayload n (o.allocations.dataCell slot)).contents i = UInt8.ofNat byte.val := by
  have data := related.image.data slot cell read
  have payload := trust.cell_payload n r.heap related.nativeHeap related.valid
    (o.allocations.dataCell slot)
  have counter := (trust.cell_counter n r.heap related.nativeHeap related.valid
    (o.allocations.dataCell slot)).1
  exact ⟨(congrArg Payload.descriptor payload).trans data.2.1,data.2.2.1,
    counter.trans data.2.2.2.1,by simpa only [payload] using data.2.2.2.2.2.2⟩

/-- Live native typed guard identity, allocation liveness and descriptor follow
from route B at this cut, rather than an integer-address/byte-havoc encoding. -/
theorem selected_token {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (trust : S2TrustedSdkBorrow L)
    (o : Originals W Child Alloc Event) (n : W) (r : OwnedCut Child Alloc Event)
    (related : CutRelated L o n r) (b : TokenBinding) (live : b ∈ r.tokens) :
    ∃ account, r.sdk.accounts.val[b.accountIndex]? = some account ∧
      L.liveGuard n b.token = some
        ⟨b.token,o.allocations.dataCell account.data_slot.val,b.owner,b.kind,
          o.allocations.descriptor account.data_slot.val⟩ ∧
      L.allocated n (o.allocations.dataCell account.data_slot.val) = true := by
  obtain ⟨a,read,guard⟩ := related.tokens b live
  have h := trust.guard_liveness n r.heap b.token _ related.nativeHeap related.valid guard
  exact ⟨a,read,h.1,h.2.1⟩

#print axioms selected_account
#print axioms selected_data
#print axioms selected_token
end AspisR1.S2H
