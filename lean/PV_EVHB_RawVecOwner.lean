import R1Z.PV_FXM_ReserveWorld
/-! RawVec descriptor ownership in the V183 world family. Source slots are
indexed by owner identity, never by element equality. This is a descriptor
interpretation, NOT yet the deployed caller's slot interpretation. Allocator
metadata transitions below specify returning Global/System semantics; their
native adequacy remains rdea-1. In particular finish_grow returns a pending
allocation, not ownership of the still-unmodified RawVec header. -/
set_option autoImplicit false
namespace PV_EVHB_RawVecOwner
open R1Z.PV_FXM_ReserveWorld

structure Allocation where
  bytes : Nat
  alignment : Aeneas.Std.core.ptr.alignment.Alignment

structure Heap (S : Type) where
  backend : S
  metadata : Nat → Option Allocation

/-- cap is the STORED RawVecInner.cap, not capacity() for a ZST. The boolean
records the source dangling-pointer constructor, not an address-only guess. -/
structure Header where
  pointer : Nat
  cap : Nat
  len : Nat
  shape : Shape
  dangling : Bool

structure Frame (F : Type) where
  rest : F
  slots : Nat → Option Header

abbrev NativeWorld (S F : Type) := World (Heap S) (Frame F)

def lookup {S F : Type} (w : NativeWorld S F) (owner : Nat) : Option Header :=
  w.frame.slots owner

def layout (h : Header) (cap : Nat) : Allocation :=
  ⟨cap*h.shape.width,h.shape.align⟩

/-- The requested allocation-or-unallocated relation, for physical RawVec cap.
Length validity and element initialization are separate source invariants. -/
def Owned {S F : Type} (w : NativeWorld S F) (h : Header) : Prop :=
  (w.allocator.metadata h.pointer = some (layout h h.cap) ∧ w.live h.pointer = true) ∨
  (h.dangling = true ∧ h.cap = 0)

def OwnedAt {S F : Type} (w : NativeWorld S F) (owner : Nat) : Prop :=
  ∃ h, lookup w owner = some h ∧ Owned w h

def store {S F : Type} (w : NativeWorld S F) (owner : Nat) (h : Header) : NativeWorld S F :=
  {w with frame := {w.frame with slots := fun id => if id=owner then some h else w.frame.slots id}}

theorem lookup_store {S F : Type} (w : NativeWorld S F) (owner : Nat) (h : Header) :
    lookup (store w owner h) owner = some h := by
  simp only [lookup,store,ite_true]

theorem lookup_other {S F : Type} (w : NativeWorld S F) (owner other : Nat)
    (h : Header) (different : other≠owner) :
    lookup (store w owner h) other = lookup w other := by
  simp only [lookup,store,different,ite_false]

theorem owned_store {S F : Type} (w : NativeWorld S F) (owner : Nat) (h old : Header) :
    Owned (store w owner h) old ↔ Owned w old := Iff.rfl

def request (h : Header) (cap : Nat) : Request := ⟨h.pointer,h.cap,cap,h.shape⟩

def resizedMetadata {S : Type} (heap : Heap S) (h : Header) (pointer cap : Nat) :
    Nat → Option Allocation := fun address =>
  if address=pointer then some (layout h cap)
  else if h.cap≠0 ∧ address=h.pointer then none else heap.metadata address

/-- Returning allocation branch, before the RawVec pointer/capacity stores.
V183's attempted/succeeded retain its exact memory/live/history effects. -/
def allocated {S F : Type} (w : NativeWorld S F) (h : Header)
    (pointer cap : Nat) (backend : S) : NativeWorld S F :=
  succeeded (request h cap) pointer
    (attempted (request h cap) (some pointer)
      ⟨backend,resizedMetadata w.allocator h pointer cap⟩ w)

/-- Returning allocation denial retains metadata and live state, even though
the allocator backend and allocation history have advanced. -/
def denied {S F : Type} (w : NativeWorld S F) (h : Header)
    (cap : Nat) (backend : S) : NativeWorld S F :=
  attempted (request h cap) none ⟨backend,w.allocator.metadata⟩ w

def Pending {S F : Type} (w : NativeWorld S F) (h : Header) (pointer cap : Nat) : Prop :=
  w.allocator.metadata pointer = some (layout h cap) ∧ w.live pointer = true

theorem allocated_pending {S F : Type} (w : NativeWorld S F) (h : Header)
    (pointer cap : Nat) (backend : S) :
    Pending (allocated w h pointer cap backend) h pointer cap := by
  simp only [Pending,allocated,succeeded,attempted,resizedMetadata,ite_true]
  constructor <;> trivial

theorem allocated_lookup {S F : Type} (w : NativeWorld S F) (h : Header)
    (owner pointer cap : Nat) (backend : S) :
    lookup (allocated w h pointer cap backend) owner = lookup w owner := rfl

theorem denied_owned {S F : Type} (w : NativeWorld S F) (h old : Header)
    (cap : Nat) (backend : S) :
    Owned (denied w h cap backend) old ↔ Owned w old := Iff.rfl

theorem denied_delivery {S F : Type} (w : NativeWorld S F) (h : Header)
    (owner cap : Nat) (backend : S) :
    lookup (denied w h cap backend) owner = lookup w owner ∧
    (denied w h cap backend).allocator.backend = backend ∧
    (denied w h cap backend).history = w.history ++ [⟨request h cap,none⟩] :=
  ⟨rfl,rfl,rfl⟩

/-- Source raw_vec/mod.rs:745 then :746, retaining the same owner slot and
the old initialized length/layout. No allocator operation occurs here. -/
def pointerStore (h : Header) (pointer : Nat) : Header :=
  {h with pointer := pointer, dangling := false}

def capacityStore (h : Header) (cap : Nat) : Header := {h with cap := cap}

def install {S F : Type} (w : NativeWorld S F) (owner : Nat) (h : Header)
    (pointer cap : Nat) : NativeWorld S F :=
  store (store w owner (pointerStore h pointer)) owner
    (capacityStore (pointerStore h pointer) cap)

theorem install_lookup {S F : Type} (w : NativeWorld S F) (owner : Nat) (h : Header)
    (pointer cap : Nat) :
    lookup (install w owner h pointer cap) owner =
      some (capacityStore (pointerStore h pointer) cap) :=
  lookup_store _ _ _

theorem pending_install {S F : Type} (w : NativeWorld S F) (owner : Nat) (h : Header)
    (pointer cap : Nat) (pending : Pending w h pointer cap) :
    OwnedAt (install w owner h pointer cap) owner := by
  refine ⟨capacityStore (pointerStore h pointer) cap,install_lookup _ _ _ _ _,?_⟩
  exact Or.inl pending

theorem successful_grow_delivery {S F : Type} (w : NativeWorld S F) (owner : Nat)
    (h : Header) (pointer cap : Nat) (backend : S) :
    OwnedAt (install (allocated w h pointer cap backend) owner h pointer cap) owner ∧
    lookup (install (allocated w h pointer cap backend) owner h pointer cap) owner =
      some (capacityStore (pointerStore h pointer) cap) :=
  ⟨pending_install _ _ _ _ _ (allocated_pending _ _ _ _ _),install_lookup _ _ _ _ _⟩

/-- A moving successful realloc invalidates the old header before its stores.
This does not refute ownership at the enclosing reserve's return boundary. -/
theorem moving_finish_grow_not_owned {S F : Type} (w : NativeWorld S F) (h : Header)
    (pointer cap : Nat) (backend : S) (nonzero : h.cap≠0) (moved : h.pointer≠pointer) :
    ¬ Owned (allocated w h pointer cap backend) h := by
  intro owned
  rcases owned with old | empty
  · have dead : (allocated w h pointer cap backend).live h.pointer = false := by
      simp only [allocated,succeeded,attempted,request,moved,ite_false,nonzero,
        ne_eq,not_false_eq_true,and_self,ite_true]
    rw [dead] at old
    cases old.2
  · exact nonzero empty.2

/-- Even an in-place growth changes the requested allocation layout. The old
header's capacity is not an exact-layout owner of the new allocation. -/
theorem inplace_finish_grow_not_owned {S F : Type} (w : NativeWorld S F) (h : Header)
    (cap : Nat) (backend : S) (nonzero : h.cap≠0)
    (changed : layout h cap ≠ layout h h.cap) :
    ¬ Owned (allocated w h h.pointer cap backend) h := by
  intro owned
  rcases owned with old | empty
  · have updated : (allocated w h h.pointer cap backend).allocator.metadata h.pointer =
        some (layout h cap) := (allocated_pending _ _ _ _ _).1
    rw [updated] at old
    exact changed (Option.some.inj old.1)
  · exact nonzero empty.2

/-- RawVec::deallocate does NOT reset ptr/cap. The source slot is consumed by
Drop; a live-ownership postcondition for the old descriptor would be false. -/
def deallocated {S F : Type} (w : NativeWorld S F) (h : Header) (backend : S) : NativeWorld S F :=
  {w with allocator := ⟨backend,fun p => if p=h.pointer then none else w.allocator.metadata p⟩
          live := fun p => if p=h.pointer then false else w.live p
          deallocCalls := w.deallocCalls+1}

theorem deallocate_consumes {S F : Type} (w : NativeWorld S F) (h : Header)
    (backend : S) (nonzero : h.cap≠0) : ¬ Owned (deallocated w h backend) h := by
  intro owned
  rcases owned with old | empty
  · have dead : (deallocated w h backend).live h.pointer = false := by
      simp only [deallocated,ite_true]
    rw [dead] at old
    cases old.2
  · exact nonzero empty.2

/-- Moves transfer a source slot, preserving the header rather than searching
for another vector with the same initialized values. -/
def move {S F : Type} (w : NativeWorld S F) (source target : Nat) : NativeWorld S F :=
  {w with frame := {w.frame with slots := fun id =>
    if id=target then w.frame.slots source else if id=source then none else w.frame.slots id}}

theorem move_delivery {S F : Type} (w : NativeWorld S F) (source target : Nat)
    (different : source≠target) :
    lookup (move w source target) target = lookup w source ∧
    lookup (move w source target) source = none := by
  simp only [move,lookup,ite_true,different,ite_false]
  exact ⟨True.intro,True.intro⟩

#print axioms lookup_store
#print axioms lookup_other
#print axioms owned_store
#print axioms allocated_pending
#print axioms allocated_lookup
#print axioms denied_owned
#print axioms denied_delivery
#print axioms install_lookup
#print axioms pending_install
#print axioms successful_grow_delivery
#print axioms moving_finish_grow_not_owned
#print axioms inplace_finish_grow_not_owned
#print axioms deallocate_consumes
#print axioms move_delivery
end PV_EVHB_RawVecOwner
