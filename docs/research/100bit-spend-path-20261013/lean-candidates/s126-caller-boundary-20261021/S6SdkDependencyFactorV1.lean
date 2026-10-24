import S2W_WrapperLaws
import S2W_Trace
import S2W_EntryPrivileges
import S2W_SnapshotFacts
import AspisV8R19.SqueezeOracleBridge
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.MultiproofConeCanonical
open AspisV8R19.DuplexFrames
def bytesOf (xs : List U8) : Bytes := xs.map AspisV8R19.SqueezeOracleBridge.decodeByte
end AspisR1.MultiproofConeCanonical

namespace AspisR1.S2LeadInterface
open AspisV8R19.DuplexFrames
structure Account where
  key : Bytes
  owner : Bytes
  lamports : Nat
  data : Bytes
  signer : Bool
  writable : Bool
  executable : Bool
  rentEpoch : Nat

end AspisR1.S2LeadInterface

namespace AspisR1.S2Z.Oracle
abbrev Parts := Slice (Slice U8)
abbrev Digest := Array U8 32#usize

end AspisR1.S2Z.Oracle

namespace AspisR1.S2W_ExtractionBoundary
open Aeneas Aeneas.Std Result AspisR1.AdapterRw
abbrev Accounts := Slice Cuts.Account
abbrev Program := AdapterRw.solana_pubkey.Pubkey
abbrev Slot := core.result.Result U64 Cuts.PE
abbrev First := Program → Accounts → Slice U8 → Result (core.result.Result (alloc.vec.Vec U8) Cuts.PE)
abbrev Second := Program → Accounts → Slice U8 → Slot → Result (core.result.Result Unit Cuts.PE)

end AspisR1.S2W_ExtractionBoundary

namespace AspisR1.S2W_EntryWriteHistory
open S2Trust AspisV8R19.DuplexFrames
def payloadBytes (encode : UInt8 → AspisV8R19.DuplexFrames.Byte) (p : Payload) (n : Nat) : Bytes :=
  List.ofFn (fun i : Fin n => encode (p.contents i.val))

end AspisR1.S2W_EntryWriteHistory

namespace AspisR1.S2W_CommittedCheckpoint
open S2Trust S2W_EntryWriteHistory
def source (bytes : List UInt8) : Payload :=
  ⟨⟨0,bytes.length,0⟩,fun i => bytes[i]?.getD 0⟩

theorem source_bytes (encode : UInt8 → AspisV8R19.DuplexFrames.Byte) (bytes : List UInt8) :
    payloadBytes encode (source bytes) bytes.length = bytes.map encode := by
  apply List.ext_getElem
  · simp [payloadBytes]
  · intro i left right
    simp [payloadBytes,source]

end AspisR1.S2W_CommittedCheckpoint

namespace AspisR1.S2W_ReturnedCheckpoint
open Aeneas Aeneas.Std S2Trust S2W_WrapperLaws S2W_EntryWriteHistory S2W_CommittedCheckpoint
open MultiproofConeCanonical AspisV8R19.DuplexFrames

def encode (byte : UInt8) : AspisV8R19.DuplexFrames.Byte := byte.toFin
def nativeByte (byte : U8) : UInt8 := UInt8.ofNat byte.val
def nativeBytes (saved : alloc.vec.Vec U8) : List UInt8 := saved.val.map nativeByte

theorem byte_representation (byte : U8) :
    encode (nativeByte byte) = AspisV8R19.SqueezeOracleBridge.decodeByte byte := by
  apply Fin.ext
  change (UInt8.ofNat byte.val).toNat = byte.val
  exact UInt8.toNat_ofNat_of_lt' byte.bv.isLt

theorem vector_representation (saved : alloc.vec.Vec U8) :
    (nativeBytes saved).map encode = bytesOf saved.val := by
  simp only [nativeBytes,bytesOf,List.map_map]
  exact List.map_congr_left (fun byte _ => byte_representation byte)

end AspisR1.S2W_ReturnedCheckpoint

namespace AspisR1.S2W_AccountObservations
open S2Trust S2W_TrustedStd S2W_WrapperLaws S2W_EntryWriteHistory
open AspisV8R19.DuplexFrames

def observe {F : Type} (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat) (s : Heap F)
    (a : Nat) : S2LeadInterface.Account :=
  if a < n then
    {metadata s.ambient a with data := (payloadBytes encode (s.payload (s.accounts a).1)
      (s.payload (s.accounts a).1).descriptor.length)}
  else metadata s.ambient a

/-- Snapshot's actual shared acquire/drop bracket changes no account record.
The copy/allocation source port remains separate, as in the imported SDK law. -/
theorem snapshot_frame {F : Type} (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat) (s : Heap F)
    (keys : Nat → List UInt8) (a token owner : Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission s keys n) (within : a < n) :
    observe encode metadata n (AdapterRw.Snapshots.sharedBracket s a token owner) =
      observe encode metadata n s := by
  rw [AdapterRw.Snapshots.entry_bracket_restores runtime within token owner]

/-- Lift the checked wrapper's single-cell frame to full account records.
Alias exclusion is explicit, not inferred merely from unequal slot numbers. -/
theorem write_frame {F : Type} (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat) (s : Heap F)
    (writer token owner : Nat) (src : Payload)
    (empty : s.guards = []) (zero : s.counter (s.accounts writer).1 = 0)
    (a : Nat) (disjoint : a < n → (s.accounts a).1 ≠ (s.accounts writer).1) :
    observe encode metadata n (writeBracket s writer token owner src) a =
      observe encode metadata n s a := by
  rw [write_bracket s writer token owner src empty zero]
  by_cases within : a < n
  · simp [observe,within,copyHeap,put,disjoint within]
  · simp [observe,within,copyHeap]

/-- The written account's entire metadata record is unchanged. No account
post-state or metadata equation is a premise. -/
theorem write_metadata {F : Type} (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat) (s : Heap F)
    (writer token owner : Nat) (src : Payload)
    (empty : s.guards = []) (zero : s.counter (s.accounts writer).1 = 0) :
    {observe encode metadata n (writeBracket s writer token owner src) writer with
      data := (observe encode metadata n s writer).data} = observe encode metadata n s writer := by
  rw [write_bracket s writer token owner src empty zero]
  by_cases within : writer < n
  · simp [observe,within,copyHeap]
  · simp [observe,within,copyHeap]

/-- Runtime key/cell admission discharges the local alias-exclusion condition
for an accessible account with a different key from the checkpoint account. -/
theorem admitted_write_frame {F : Type} (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat) (s : Heap F)
    (keys : Nat → List UInt8) (writer token owner : Nat) (src : Payload)
    (runtime : AdapterRw.RuntimeEntrypointAdmission s keys n) (writerWithin : writer < n)
    (a : Nat) (different : a < n → keys a ≠ keys writer) :
    observe encode metadata n (writeBracket s writer token owner src) a =
      observe encode metadata n s a := by
  apply write_frame encode metadata n s writer token owner src runtime.freshGuards
    (runtime.counterZero writer writerWithin) a
  intro within
  exact AdapterRw.distinct_keys_distinct_cells runtime within writerWithin (different within)

#print axioms snapshot_frame
#print axioms write_frame
#print axioms write_metadata
#print axioms admitted_write_frame
end AspisR1.S2W_AccountObservations


namespace AspisR1.S2W_D189Interpretation
open S2Trust S2W_EntryWriteHistory S2W_AccountObservations
open Aeneas Aeneas.Std Result S2W_Trace

/-- Native data observation through the actual typed SDK library carrier.
The ambient parameter is the runtime metadata interpretation, not an inferred
OwnedAccount projection (which omits lamports and rentEpoch). -/
def nativeObserve {W F : Type} (L : Library W F)
    (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat)
    (w : W) (ambient : F) (a : Nat) : S2LeadInterface.Account :=
  if a < n then
    {metadata ambient a with data := (payloadBytes encode
      (L.cellPayload w (L.accountData w a))
      (L.cellPayload w (L.accountData w a)).descriptor.length)}
  else metadata ambient a

/-- The native AccountInfo/heap association is obtained from exactly the
approved account_data_cell and cell_payload fields. It is not a caller
postcondition, source equality, or new native-binding assumption. -/
theorem native_observation {W F : Type} (L : Library W F)
    (sdk : S2TrustedSdkBorrow L)
    (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat)
    (w : W) (s : Heap F) (related : L.related w s) (valid : Valid s) :
    nativeObserve L encode metadata n w s.ambient = observe encode metadata n s := by
  funext a
  have cell := (sdk.account_data_cell w s related valid a a).1
  have payload := sdk.cell_payload w s related valid (s.accounts a).1
  simp only [nativeObserve,observe,cell,payload]

/-- The native counter/guard ledger is the SAME heap's ledger. -/
theorem native_counter {W F : Type} (L : Library W F)
    (sdk : S2TrustedSdkBorrow L) (w : W) (s : Heap F)
    (related : L.related w s) (valid : Valid s) (c : Nat) :
    L.cellCounter w c = s.counter c ∧ ∀ t, L.liveGuard w t = lookup s t :=
  sdk.cell_counter w s related valid c

end AspisR1.S2W_D189Interpretation

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
    refine ⟨bytes,rfl,?_⟩
    simpa only [AdapterRw.r1_pool_adapter.owned.OwnedAccount.data,stored,
      Result.ok.injEq,core.result.Result.Ok.injEq] using success
  | Err error =>
    unfold AdapterRw.r1_pool_adapter.owned.OwnedAccount.data at success
    rw [stored] at success
    exact False.elim (Cuts.error_bind_ne_ok (ownedOps.op35 error) data success)

end AspisR1.S2W.SnapshotJoin

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
  ⟨[e.snapshot 0 58295 58295,e.snapshot 1 1880 1880,e.snapshot 2 1768 1768],by simp only [List.length_cons,List.length_nil]; scalar_tac⟩

def Entry.second (e : Entry) (sizes : Nat → Nat × Nat) : S2W_ExtractionBoundary.Accounts :=
  ⟨List.ofFn (fun i : Fin 7 => e.snapshot i.val (sizes i.val).1 (sizes i.val).2),by simp only [List.length_ofFn]; scalar_tac⟩

 theorem first_index (e : Entry) :
    Slice.index_usize e.first 0#usize = ok (e.snapshot 0 58295 58295) ∧
    Slice.index_usize e.first 1#usize = ok (e.snapshot 1 1880 1880) ∧
    Slice.index_usize e.first 2#usize = ok (e.snapshot 2 1768 1768) := by
  exact ⟨rfl,rfl,rfl⟩

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
      (e.buffers (e.handles 2).1).val.length = 1768 then core.result.Result.Ok (e.buffers (e.handles 2).1)
      else core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) =
      core.result.Result.Ok copied at stored
  split at stored
  · rename_i size
    exact size.elim id id
  · cases stored

/-- Canonical byte representation of the original native account buffer. -/
theorem payload_bytes (e : Entry) (c : Nat) :
    payloadBytes encode (e.payload c) (e.payload c).descriptor.length = bytesOf (e.buffers c).val := by
  change payloadBytes encode (source (nativeBytes (e.buffers c))) (e.buffers c).val.length = _
  have size : (nativeBytes (e.buffers c)).length = (e.buffers c).val.length := by
    simp only [nativeBytes,List.length_map]
  rw [← size,source_bytes,vector_representation]

/-- The SDK data descriptor exposes exactly the original finite native buffer,
not a post-execution read of an allegedly identical allocation. -/
theorem native_buffer {W : Type} (e : Entry) (L : Library W (Nat → Record))
    (sdk : S2TrustedSdkBorrow L) (w : W) (related : L.related w e.heap)
    (valid : Valid e.heap) (a : Nat) :
    payloadBytes encode (L.cellPayload w (L.accountData w a))
      (L.cellPayload w (L.accountData w a)).descriptor.length =
      bytesOf (e.buffers (e.handles a).1).val := by
  rw [(sdk.account_data_cell w e.heap related valid a a).1,
    sdk.cell_payload w e.heap related valid (e.heap.accounts a).1]
  exact payload_bytes e (e.handles a).1

#print axioms payload_bytes
#print axioms native_buffer
#print axioms first_index
#print axioms first_disjoint
#print axioms checkpoint_size
end AspisR1.S2W_D189Entry

namespace AspisR1.S2W_D189Wrappers
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_CommittedCheckpoint

/-- Runtime allocator interface on its private region. P2-P4 admit this
separation from account cells. Allocation or cleanup failure aborts; the
caller proves nothing about an aborted transaction's committed accounts. -/
structure Allocator (A : Type) where
  allocate : A → Nat → Result A
  cleanup : A → Result A

def reserve {A : Type} (allocator : Allocator A) : List Nat → A → Result A
  | [], state => ok state
  | size :: sizes, state => S2W_Trace.thenResult (allocator.allocate state size)
      (fun next => reserve allocator sizes next)

def admittedSizes (e : Entry) (count : Nat) (sizes : Nat → Nat × Nat) : List Nat :=
  (List.range count).filterMap (fun a =>
    let len := (e.buffers (e.handles a).1).val.length
    if len = (sizes a).1 ∨ len = (sizes a).2 then some len else none)

def firstSizes : Nat → Nat × Nat
  | 0 => (58295,58295) | 1 => (1880,1880) | _ => (1768,1768)

def secondSizes : Nat → Nat × Nat
  | 0 => (58295,58295) | 1 => (384,384) | 2 => (192,192)
  | 3 => (768,768) | 4 => (128,256) | 5 => (192,320) | _ => (1768,1768)

/-- Account-only state extension of std Vec allocation/cleanup. to_vec's
complete byte law is Snapshot.to_vec_identity; the allocator does not receive
an AccountInfo or a heap capability. This is the runtime allocator premise's
interpretation, not a claim that allocator state remains unchanged. -/
def allocateSnapshots {A : Type} (allocator : Allocator A) (e : Entry)
    (count : Nat) (sizes : Nat → Nat × Nat) (state : A) :
    Result (A × Heap (Nat → Record)) :=
  S2W_Trace.thenResult (reserve allocator (admittedSizes e count sizes) state)
    (fun next => ok (next,e.heap))

 theorem allocation_frame {A : Type} (allocator : Allocator A) (e : Entry)
    (count : Nat) (sizes : Nat → Nat × Nat) (state next : A) (heap : Heap (Nat → Record))
    (returned : allocateSnapshots allocator e count sizes state = ok (next,heap)) :
    heap = e.heap := by
  unfold allocateSnapshots at returned
  cases allocated : reserve allocator (admittedSizes e count sizes) state with
  | fail error => simp [allocated,S2W_Trace.thenResult] at returned
  | div => simp [allocated,S2W_Trace.thenResult] at returned
  | ok value =>
    simp only [allocated,S2W_Trace.thenResult] at returned
    exact (congrArg Prod.snd (Result.ok.inj returned)).symm

/-- The native first wrapper: same snapshot bounds, owned call, one mutable
borrow/copy/drop, then owned-Vec cleanup. SDK acquisition/drop use the approved
interpretation; bulk copy is the separately named TrustedStd primitive. -/
def first {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (program : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (state : A) :
    Result (core.result.Result (alloc.vec.Vec U8 × Heap (Nat → Record) × A) AdapterRw.Cuts.PE) := do
  let allocated ← reserve allocator (admittedSizes e 3 firstSizes) state
  let result ← native program e.first data
  match result with
  | .Err error => ok (.Err error)
  | .Ok saved =>
    match copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive) (e.heap.accounts 2).1
        (source (nativeBytes saved)) with
    | .panic => .fail .assertionFailure
    | .returned written =>
      let cleaned ← allocator.cleanup allocated
      ok (.Ok (saved,release written (exclusiveGuard e.heap 2 0 0),cleaned))

def second {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (program : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state : A) :
    Result (core.result.Result (Heap (Nat → Record) × A) AdapterRw.Cuts.PE) := do
  let allocated ← reserve allocator (admittedSizes e 7 secondSizes) state
  let result ← native program (e.second secondSizes) data slot
  match result with
  | .Err error => ok (.Err error)
  | .Ok () =>
    let cleaned ← allocator.cleanup allocated
    ok (.Ok (e.heap,cleaned))

/-- Invert wrapper acceptance. The actual returned heap is derived from the
single trusted std copy; no savedAtWrite or after-account observation supplied. -/
theorem first_accepted {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (after : Heap (Nat → Record))
    (accepted : first native copy allocator e program data state = ok (.Ok (saved,after,final))) :
    native program e.first data = ok (.Ok saved) ∧
    after = writeBracket e.heap 2 0 0 (source (nativeBytes saved)) := by
  unfold first at accepted
  obtain ⟨allocated,_,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
  obtain ⟨result,called,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  cases result with
  | Err error => cases rest
  | Ok value =>
    dsimp only at rest
    cases copied : copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive)
        (e.heap.accounts 2).1 (source (nativeBytes value)) with
    | panic => simp only [copied] at rest; cases rest
    | returned written =>
      rw [copied] at rest
      obtain ⟨cleaned,_,returned⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
      have equal := core.result.Result.Ok.inj (Result.ok.inj returned)
      have same : value = saved := congrArg Prod.fst equal
      subst value
      refine ⟨called,?_⟩
      have actual := std.slice_copy_from_slice
        (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive) (e.heap.accounts 2).1
        (source (nativeBytes saved))
      rw [copied] at actual
      unfold specification at actual
      split at actual
      · have w := Outcome.returned.inj actual
        rw [w] at equal
        exact (congrArg (fun pair => pair.2.1) equal).symm
      · cases actual

 theorem second_accepted {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (program : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state final : A)
    (after : Heap (Nat → Record))
    (accepted : second native allocator e program data slot state = ok (.Ok (after,final))) :
    native program (e.second secondSizes) data slot = ok (.Ok ()) ∧ after = e.heap := by
  unfold second at accepted
  obtain ⟨allocated,_,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
  obtain ⟨result,called,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  cases result with
  | Err error => cases rest
  | Ok value =>
    obtain ⟨cleaned,_,returned⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
    have equal := core.result.Result.Ok.inj (Result.ok.inj returned)
    exact ⟨called,(congrArg Prod.fst equal).symm⟩

#print axioms allocation_frame
#print axioms first_accepted
#print axioms second_accepted
end AspisR1.S2W_D189Wrappers

namespace AspisR1.S2W_DigestExtraction
open Aeneas Aeneas.Std Result
open S2W_ExtractionBoundary
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Parts := S2Z.Oracle.Parts
abbrev Digest := S2Z.Oracle.Digest

/-- Exact emitted Hash::to_bytes body; Hash is emitted as Array U8 32. -/
def toBytes (self : Digest) : Result Digest := do
  ok self

/-- Exact emitted source digest body after the recorded single external-callee
substitution and nominal carrier reuse. Neither success nor totality assumed. -/
def digest (hashv : Parts → Result Digest) (self : AdapterRw.SolanaDigest)
    (parts : Parts) : Result Digest := do
  let h ← hashv parts
  toBytes h

/-- Source wrapper contributes no extra value or termination premise. -/
theorem digest_eq_hashv (hashv : Parts → Result Digest) (self : AdapterRw.SolanaDigest)
    (parts : Parts) : digest hashv self parts = hashv parts := by
  unfold digest toBytes
  cases hashv parts <;> rfl

/-- D188 extraction trust refers to the EXTRACTED source wrapper here, rather
than treating its old opaque op43 as already proved to be hashv. These are
source-function interpretation equalities, not any caller field or conclusion.
The code identity/reused emission audit is explicit in the evidence packet. -/
structure AeneasExtraction (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : Parts → Result Digest) : Prop where
  stage1 : ∀ program accounts data,
    native1 program accounts data = AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data
  stage2 : ∀ program accounts data slot,
    native2 program accounts data slot = AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts data slot
  digestSource : ∀ self parts, ops.op43 self parts = digest hashv self parts

end AspisR1.S2W_DigestExtraction

namespace AspisR1.S2W_D189Consolidation
open S2Trust S2W_D189Entry S2W_ReturnedCheckpoint
structure RuntimeEntrypointAdmission {W : Type} (L : Library W (Nat → Record))
    (e : Entry) (w : W) (n : Nat) : Prop where
  entry : AdapterRw.RuntimeEntrypointAdmission e.heap
    (fun a => (e.records (e.handles a).1).owned.key.val.map nativeByte) n
  related : L.related w e.heap
end AspisR1.S2W_D189Consolidation

end
