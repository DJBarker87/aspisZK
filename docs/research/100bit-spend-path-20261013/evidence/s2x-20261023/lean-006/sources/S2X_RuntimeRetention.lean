import S2X_SnapshotWrite
import R9PoolRuntimeBinding

/-! Existing P2′ is used verbatim. P2/P3/P4 in BoundaryStatements are opaque
Props, so their required operational interpretation is stated separately and
not falsely inferred from BoundaryEvidence. No new runtime trust is adopted. -/
set_option autoImplicit false
namespace AspisR1.S2X
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open R9PoolRuntimeBinding S2LeadInterface

/-- Native child source-refinement obligation. Oracle and child-private
allocator state may change. Account records, caller-owned payloads and their
allocation liveness must not. Includes lamports and metadata through Account.
This is not implied by pure Lean argument retention or an opaque Ops result. -/
structure OpaqueChildFrame {W : Type}
    (accounts : W → Nat → S2LeadInterface.Account)
    (payload : W → Nat → S2Trust.Payload) (allocated : W → Nat → Bool)
    (owned : Nat → Prop) (before after : W) : Prop where
  accountRecords : ∀ a, accounts after a = accounts before a
  ownedPayload : ∀ a, owned a → payload after a = payload before a
  ownedLive : ∀ a, owned a → allocated after a = allocated before a

/-- Full proof-account equality across TXs is NOT required: P2′ binds the
consumed proof slice after the successful digest checks. It permits adversarial
uploads and changing raw candidate prefixes. This is exactly the existing P2′. -/
theorem tx2_proof_binding (hash : Bytes → State) (written current : R9PoolRuntimeBinding.Inputs)
    (p2prime : P2Prime hash written current) (matched : digestMatches hash written current) :
    current.proof = written.proof ∧ current.pub = written.pub := p2prime matched

/-- Source range plus the existing P2′ premise yields the Required14 suffix
shape for the actual TX2 account, without asserting full raw-account retention. -/
theorem tx2_suffix (hash : Bytes → State) (written current : R9PoolRuntimeBinding.Inputs)
    (p2prime : P2Prime hash written current) (matched : digestMatches hash written current)
    (raw selected : Slice U8) (finish : Usize)
    (length : raw.val.length = finish.val) (ordered : (688#usize).val ≤ finish.val)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      raw {start := 688#usize, «end» := finish} = ok selected)
    (actualCurrent : bytesOf selected.val = current.proof) :
    bytesOf raw.val = (bytesOf raw.val).take 688 ++ written.proof := by
  have shape := (AdapterRw.Ranges.suffix_exact raw selected 688#usize finish ordered length range).2
  have mapped := congrArg bytesOf shape
  have bytes : bytesOf raw.val = (bytesOf raw.val).take 688 ++ bytesOf selected.val := by
    simpa only [bytesOf,List.map_append,List.map_take] using mapped
  rw [actualCurrent,(p2prime matched).1] at bytes
  exact bytes

/-- Runtime transaction effects relevant to persistence. Failed transactions
have no committed account writes. Successful transactions may write other
accounts. This is a small history specification, not extracted Solana code. -/
inductive AccountEvent where
  | committedWrite (account : Nat) (bytes : Bytes)
  | rollback

def applyEvent (ledger : Nat → Bytes) : AccountEvent → Nat → Bytes
  | .committedWrite a bytes => fun b => if b = a then bytes else ledger b
  | .rollback => ledger

def history (ledger : Nat → Bytes) : List AccountEvent → Nat → Bytes
  | [] => ledger
  | event :: rest => history (applyEvent ledger event) rest

def Preserves (account : Nat) : AccountEvent → Prop
  | .committedWrite a _ => account ≠ a
  | .rollback => True

/-- P2 persistence/rollback interpreted on a history with no intervening
committed write to the protected version. Readonly status in TX2 alone does
not establish this premise. -/
theorem history_retains (ledger : Nat → Bytes) (events : List AccountEvent) (account : Nat)
    (protected : ∀ event ∈ events, Preserves account event) :
    history ledger events account = ledger account := by
  induction events generalizing ledger with
  | nil => rfl
  | cons event rest ih =>
    rw [history, ih (applyEvent ledger event) (by
      intro e he
      exact protected e (List.mem_cons_of_mem event he))]
    have head := protected event (by simp only [List.mem_cons, true_or])
    cases event with
    | rollback => rfl
    | committedWrite a bytes => exact if_neg head

/-- Exact missing *interpretation* of existing runtime premises for a concrete
save/load pair. P3 authentication identifies the same ledger key/version; P4
identifies observed bytes/metadata; P2 identifies committed history/rollback.
This is NOT a new cryptographic premise and NOT an arbitrary-runtime discharge.
The protected-version condition must be justified by actual permissions/history. -/
structure CheckpointVersionBinding (saved loaded : Bytes) where
  key : Nat
  ledger : Nat → Bytes
  events : List AccountEvent
  savedAtCommit : ledger key = saved
  loadedAtEntry : loaded = history ledger events key
  noInterveningWrite : ∀ event ∈ events, Preserves key event

theorem checkpoint_persistence (saved loaded : Bytes)
    (runtime : CheckpointVersionBinding saved loaded) : loaded = saved := by
  rw [runtime.loadedAtEntry, history_retains runtime.ledger runtime.events runtime.key
    runtime.noInterveningWrite, runtime.savedAtCommit]

/-- Propagation to save/tx2/resume requires their actual source observations.
No claim is made that persistence manufactures an observation or call trace. -/
theorem checkpoint_sites {Observer : Type} (c : S2LeadInterface.Inputs Observer)
    (saved loaded : Bytes) (runtime : CheckpointVersionBinding saved loaded)
    (saveCut : c.reached .save → bytesOf (c.checkpoint .save).val = saved)
    (tx2Cut : c.reached .tx2 → bytesOf (c.checkpoint .tx2).val = loaded)
    (resumeCut : c.reached .resume → bytesOf (c.checkpoint .resume).val = loaded) :
    ∀ s, c.reached s → s = .save ∨ s = .tx2 ∨ s = .resume →
      bytesOf (c.checkpoint s).val = saved := by
  intro s reached site
  rcases site with h | h | h <;> subst s
  · exact saveCut reached
  · exact (tx2Cut reached).trans (checkpoint_persistence saved loaded runtime)
  · exact (resumeCut reached).trans (checkpoint_persistence saved loaded runtime)

#print axioms tx2_proof_binding
#print axioms tx2_suffix
#print axioms history_retains
#print axioms checkpoint_persistence
#print axioms checkpoint_sites
end AspisR1.S2X
