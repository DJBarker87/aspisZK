import PV_EVHB_RawVecSource
import R1Z.PV_RunJoin_AllocatorWorld63
/-! Returning projection registry. Selection uses a source-place identity,
never erased element equality. The source store law below relates the recorded
descriptor to RawVec's actual modeled pointer/capacity stores. This is NOT yet
the original callers' native receiver interpretation or a v263 installation.
Nonreturning primitive outcomes remain in RawVecSource, not this returning
Option-pointer projection. No native nonreturn is identified with denial. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_OwnerRegistry
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_FXM_ReserveWorld PV_EVHB_RawVecOwner

structure Descriptor where
  address : Nat
  capacity : Nat

structure State (S : Type) where
  backend : S
  current : Nat
  table : Nat → Descriptor

def descriptor : Option Header → Descriptor
  | none => ⟨0,0⟩
  | some h => ⟨h.pointer,PV_EVHB_RawVecSource.capacity Usize.max h⟩

def fromSource {S F : Type} (owner : Nat) (w : NativeWorld S F) : State (Heap S) :=
  ⟨w.allocator,owner,fun place => descriptor (lookup w place)⟩

def project {S F : Type} (owner : Nat) (w : NativeWorld S F) : World (State (Heap S)) F :=
  {allocator := fromSource owner w
   allocCalls := w.allocCalls
   reallocCalls := w.reallocCalls
   deallocCalls := w.deallocCalls
   successfulAlloc := w.successfulAlloc
   successfulRealloc := w.successfulRealloc
   drops := w.drops
   history := w.history
   memory := w.memory
   live := w.live
   frame := w.frame.rest}

/-- This source association is obtained by lookup of the same place, not by
looking for a vector with equal elements. It remains to bind those places to
the ORIGINAL reached callers. -/
theorem source_lookup {S F : Type} (owner : Nat) (w : NativeWorld S F)
    (h : Header) (selected : lookup w owner=some h) :
    (fromSource owner w).table (fromSource owner w).current=
      ⟨h.pointer,PV_EVHB_RawVecSource.capacity Usize.max h⟩ := by
  simp only [fromSource,selected,descriptor]

/-- Successful source stores deliver exactly the recorded descriptor for the
same owner. ZST growth is rejected before these stores by grow_exact/amortized. -/
theorem source_install {S F : Type} (owner : Nat) (w : NativeWorld S F)
    (h : Header) (pointer cap : Nat) (sized : h.shape.width≠0) :
    (fromSource owner (install w owner h pointer cap)).table owner=⟨pointer,cap⟩ := by
  change descriptor (lookup (install w owner h pointer cap) owner)=_
  rw [install_lookup]
  simp only [descriptor,PV_EVHB_RawVecSource.capacity,capacityStore,pointerStore,if_neg sized]

theorem source_install_table {S F : Type} (owner : Nat) (w : NativeWorld S F)
    (h : Header) (pointer cap : Nat) (sized : h.shape.width≠0) :
    (fromSource owner (install w owner h pointer cap)).table=
      fun place => if place=owner then ⟨pointer,cap⟩ else (fromSource owner w).table place := by
  funext place
  by_cases same : place=owner
  · subst place
    simpa only [ite_true] using source_install owner w h pointer cap sized
  · simp only [fromSource,lookup,install,store,same,ite_false]

def afterAnswer {S : Type} (r : Request) (answer : Option Nat) (backend : S)
    (before : State S) : State S :=
  ⟨backend,before.current,fun owner =>
    match answer with
    | none => before.table owner
    | some pointer => if owner=before.current then ⟨pointer,r.newCapacity⟩ else before.table owner⟩

/-- The registry records the post-store descriptor of a RETURNING reserve
macro-step. Relating that macro-step to finish_grow followed by source stores
requires source_install and the actual primitive returning projection; it is
not an extra action performed by the native allocator. -/
def step {S : Type} (backendStep : Request → S → Option Nat × S)
    (r : Request) (before : State S) : Option Nat × State S :=
  let (answer,backend) := backendStep r before.backend
  (answer,afterAnswer r answer backend before)

variable [ExternalTypes]

/-- Total extension to unrelated erased vectors is required by V183's type.
At a corresponding owned source vector, fits makes max return its physical
(or ZST public) capacity, as source_metadata proves. -/
def metadata {A S F : Type} (w : World (State S) F) (v : alloc.vec.Vec A) :
    R1Z.PV_FXM_ReserveSelected.Metadata v :=
  let d := w.allocator.table w.allocator.current
  ⟨d.address,max d.capacity v.val.length,Nat.le_max_right _ _⟩

def runtime {S F : Type} (backendStep : Request → S → Option Nat × S)
    (shape : Type → Shape) (encode : PV_EVHB_RawVecSource.ReserveError → alloc.collections.TryReserveError) :
    R1Z.PV_RunJoin_AllocatorWorld63.Runtime (State S) F :=
  {step := step backendStep
   shape := shape
   metadata := fun w {A} v => metadata (A := A) w v
   encode := encode}

theorem source_metadata {A S F : Type} (owner : Nat) (w : NativeWorld S F)
    (h : Header) (selected : lookup w owner=some h) (v : alloc.vec.Vec A)
    (fits : v.val.length≤PV_EVHB_RawVecSource.capacity Usize.max h) :
    (metadata (project owner w) v).address=h.pointer ∧
    (metadata (project owner w) v).capacity=PV_EVHB_RawVecSource.capacity Usize.max h := by
  simp only [metadata,project,fromSource,selected,descriptor,Nat.max_eq_left fits]
  exact ⟨True.intro,True.intro⟩

/-- Header delivery for the CONSTRUCTED returning projection, not an assumed
law of an arbitrary Runtime. The original reached-state/native association
is deliberately not claimed by this theorem. -/
theorem finish_delivery {A S F : Type} (backendStep : Request → S → Option Nat × S)
    (shape : Shape) (w : World (State S) F) (v : alloc.vec.Vec A) (n : Nat) :
    let e := finish (step backendStep) shape
      (R1Z.PV_FXM_ReserveSelected.buffer v (metadata w v)) n w
    (metadata e.world v).address=e.buffer.address ∧
    (metadata e.world v).capacity=e.buffer.capacity := by
  dsimp only [finish,step,R1Z.PV_FXM_ReserveSelected.buffer]
  cases reply : backendStep
      ⟨(metadata w v).address,(metadata w v).capacity,v.val.length+n,shape⟩
      w.allocator.backend with
  | mk answer backend =>
    cases answer with
    | none =>
      simp [attempted,metadata,afterAnswer]
    | some pointer =>
      simp [attempted,succeeded,metadata,afterAnswer,
        Nat.max_eq_left (Nat.le_add_right v.val.length n)]

theorem registered_header_delivery {A S F : Type} (backendStep : Request → S → Option Nat × S)
    (shape : Type → Shape) (encode : PV_EVHB_RawVecSource.ReserveError → alloc.collections.TryReserveError)
    (w : World (State S) F) (v : alloc.vec.Vec A) (n : Usize) :
    let r : R1Z.PV_RunJoin_AllocatorWorld63.Runtime (State S) F := runtime backendStep shape encode
    let e := R1Z.PV_RunJoin_AllocatorWorld63.execute r w v n
    (r.metadata e.world v).address=e.buffer.address ∧
    (r.metadata e.world v).capacity=e.buffer.capacity := by
  dsimp only [R1Z.PV_RunJoin_AllocatorWorld63.execute,runtime]
  unfold native growExact
  split <;> try exact ⟨rfl,rfl⟩
  split <;> try exact ⟨rfl,rfl⟩
  split <;> try exact ⟨rfl,rfl⟩
  split <;> try exact ⟨rfl,rfl⟩
  exact finish_delivery backendStep (shape A) w v n.val

#print axioms source_lookup
#print axioms source_install
#print axioms source_install_table
#print axioms source_metadata
#print axioms finish_delivery
#print axioms registered_header_delivery
end PV_EVHB_OwnerRegistry
