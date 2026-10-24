import S2W_TrustedStd
import AdapterRwSdkSnapshots

/-! Full-payload interpretation of the selected-cell wrapper checks.
The native SDK protocol theorem uses actual Library.run transitions. The
bulk copy theorem is about the authorized TrustedStd heap interpretation.
It does not identify a projected Rust type with an AccountInfo ABI value. -/
set_option autoImplicit false
namespace AspisR1.S2W_WrapperLaws
open S2Trust S2W_TrustedStd AdapterRw

structure Projection where
  length : Nat
  index : Nat
  byte : UInt8
  deriving DecidableEq

def project (p : Payload) (i : Nat) : Projection :=
  ⟨p.descriptor.length,i,p.contents i⟩

/-- The scalar copy interpretation used by Kani commutes with full-payload
copy at every accessible index. The source index/length are not extra axioms. -/
theorem copy_projection (dst src : Payload) (i : Nat)
    (within : i < dst.descriptor.length) :
    project (copied dst src) i =
      ⟨dst.descriptor.length,i,(project src i).byte⟩ := by
  simp only [project,copied,if_pos within]

/-- Extensional lift of the arbitrary-coordinate contract. No concrete array
or recurrence is reduced. Descriptor identity comes from slice geometry. -/
theorem lift_projection (dst src after : Payload)
    (descriptor : after.descriptor = dst.descriptor)
    (cells : ∀ i, (project after i).byte =
      if i < dst.descriptor.length then (project src i).byte else (project dst i).byte) :
    after = copied dst src :=
  cells_compose dst src after descriptor cells

/-- All three actual SDK operation cuts are produced from the initial native
state, not supplied as caller-success observations. Copy allocation is outside
this borrow-only protocol: its account frame must be composed separately. -/
theorem native_snapshot_protocol {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (w : W) (s : Heap F)
    (keys : Nat → List UInt8) (n a t o : Nat)
    (runtime : RuntimeEntrypointAdmission s keys n) (within : a < n)
    (related : L.related w s) :
    ∃ acquired read done,
      L.run w (.shared a t o) = (acquired,.guard t) ∧
      L.run acquired (.deref t) = (read,.payload (s.payload (s.accounts a).1)) ∧
      L.run read (.drop t) = (done,.unit) ∧ L.related done s := by
  obtain ⟨acquired,first,related1⟩ :=
    Snapshots.native_entry_shared L trust w s keys n a t o runtime within related
  obtain ⟨read,second,related2⟩ :=
    Snapshots.native_entry_read L trust acquired s keys n a t o runtime within related1
  obtain ⟨done,third,related3⟩ :=
    Snapshots.native_entry_drop L trust read s keys n a t o runtime within related2
  exact ⟨acquired,read,done,first,second,third,related3⟩

def exclusiveGuard {F : Type} (s : Heap F) (a t o : Nat) : Guard :=
  ⟨t,(s.accounts a).1,o,.exclusive,(s.payload (s.accounts a).1).descriptor⟩

def writeBracket {F : Type} (s : Heap F) (a t o : Nat) (src : Payload) : Heap F :=
  release (copyHeap (acquire s (s.accounts a).1 t o .exclusive) (s.accounts a).1 src)
    (exclusiveGuard s a t o)

/-- Borrow counter and guard cleanup commute with the single exact data copy.
This is the wrapper's full heap equation, not only an observed byte equality. -/
theorem write_bracket {F : Type} (s : Heap F) (a t o : Nat) (src : Payload)
    (empty : s.guards = []) (zero : s.counter (s.accounts a).1 = 0) :
    writeBracket s a t o src = copyHeap s (s.accounts a).1 src := by
  have counters : put (put s.counter (s.accounts a).1 (-1)) (s.accounts a).1 0 = s.counter := by
    funext c
    by_cases same : c = (s.accounts a).1
    · subst c; simp [put,zero]
    · simp [put,same]
  simp [writeBracket,exclusiveGuard,release,copyHeap,acquire,empty,counters]

/-- Every accessible checkpoint byte and every account/metadata/other-cell
frame follows after acquire/copy/drop. No separate savedAtWrite is assumed. -/
theorem checkpoint_write {F : Type} (s : Heap F) (a t o : Nat) (src : Payload)
    (empty : s.guards = []) (zero : s.counter (s.accounts a).1 = 0)
    (length : (s.payload (s.accounts a).1).descriptor.length = 1768) :
    (∀ i, i < 1768 → ((writeBracket s a t o src).payload (s.accounts a).1).contents i = src.contents i) ∧
    (writeBracket s a t o src).ambient = s.ambient ∧
    (writeBracket s a t o src).accounts = s.accounts ∧
    (writeBracket s a t o src).counter = s.counter ∧
    (∀ c, c ≠ (s.accounts a).1 → (writeBracket s a t o src).payload c = s.payload c) := by
  rw [write_bracket s a t o src empty zero]
  refine ⟨?_,rfl,rfl,rfl,?_⟩
  · intro i hi
    simp [copyHeap,put,copied,length,hi]
  · intro c hc
    exact (copy_frame s (s.accounts a).1 src).2.2.2.2.2.2.2.2 c hc

#print axioms copy_projection
#print axioms lift_projection
#print axioms native_snapshot_protocol
#print axioms write_bracket
#print axioms checkpoint_write
end AspisR1.S2W_WrapperLaws
