import AspisV8R19.R482PackedAllocationRead
import AspisV8R19.R475PointerWordRuntime

/-! Explicit shared-reference/read-place fragment for the selected raw
dereference. Live allocation and read permission are checked rather than
erased by pointer casts. Unsupported denotes no justified fragment execution;
it is not an invented Rust error. Binding these rules to native Rust validity
and the actual caller remains a separate source-semantics obligation. -/
set_option autoImplicit false
namespace AspisV8R19.R483SharedReadPlace
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R475PointerWordRuntime
open AspisV8R19.R481NativeQM31Cell
open AspisV8R19.R482PackedAllocationRead
open AspisR156FullFreeze AspisR156FullFreeze.aspis_core

structure SharedRef where
  pointer : WordPointer
  allocation : Nat

inductive Value where
  | rawMut (pointer : WordPointer)
  | shared (reference : SharedRef)
  | qm31 (value : field.QM31)

structure State where
  heap : Heap (BitVec 128)
  alive : Nat → Bool
  readable : Nat → Bool
  locals : Nat → Option Value

def put (state : State) (dst : Nat) (value : Option Value) : State :=
  { state with locals := fun slot => if slot = dst then value else state.locals slot }

def readPacked (state : State) (ptr : WordPointer) : Option (BitVec 128) := do
  let (id, _) ← ptr.origin
  if state.alive id && state.readable id then
    AspisV8R19.R432PointerPrimitive.read state.heap (decodePointer ptr)
  else none

def acquireShared (state : State) (ptr : WordPointer) : Option SharedRef := do
  let (id, _) ← ptr.origin
  let _ ← readPacked state ptr
  some ⟨ptr, id⟩

def copyShared (state : State) (reference : SharedRef) : Option field.QM31 := do
  let (id, _) ← reference.pointer.origin
  if id = reference.allocation then
    (readPacked state reference.pointer).map decodeQM31
  else none

inductive Outcome where
  | supported (state : State)
  | unsupported (state : State)

def Outcome.state : Outcome → State
  | .supported state => state
  | .unsupported state => state

-- Ref(Shared, Projection(Local(src), Deref)), assigned to local dst.
def refSharedDeref (state : State) (dst src : Nat) : Outcome :=
  match state.locals src with
  | some (.rawMut ptr) =>
      match acquireShared state ptr with
      | some reference => .supported (put state dst (some (.shared reference)))
      | none => .unsupported state
  | _ => .unsupported state

-- Copy(Projection(Local(src), Deref)), assigned to local dst.
def copySharedDeref (state : State) (dst src : Nat) : Outcome :=
  match state.locals src with
  | some (.shared reference) =>
      match copyShared state reference with
      | some value => .supported (put state dst (some (.qm31 value)))
      | none => .unsupported state
  | _ => .unsupported state

def frame (before after : State) : Prop :=
  after.heap = before.heap ∧ after.alive = before.alive ∧
    after.readable = before.readable

theorem put_frame (state : State) (dst : Nat) (value : Option Value) :
    frame state (put state dst value) := by exact ⟨rfl, rfl, rfl⟩

theorem refSharedDeref_frame (state : State) (dst src : Nat) :
    frame state (refSharedDeref state dst src).state := by
  unfold refSharedDeref
  split
  · split <;> simp [Outcome.state, frame, put]
  · rfl

theorem copySharedDeref_frame (state : State) (dst src : Nat) :
    frame state (copySharedDeref state dst src).state := by
  unfold copySharedDeref
  split
  · split <;> simp [Outcome.state, frame, put]
  · rfl

theorem copy_acquired (state : State) (ptr : WordPointer)
    (reference : SharedRef) (h : acquireShared state ptr = some reference) :
    copyShared state reference = (readPacked state ptr).map decodeQM31 := by
  cases ho : ptr.origin with
  | none => simp [acquireShared, ho] at h
  | some pair =>
      rcases pair with ⟨id, offset⟩
      cases hr : readPacked state ptr with
      | none => simp [acquireShared, ho, hr] at h
      | some cell =>
          simp [acquireShared, ho, hr] at h
          subst reference
          simp [copyShared, ho]

theorem readPacked_backed (state : State) (id : Nat)
    (a : Allocation (BitVec 128)) (hlookup : state.heap id = some a)
    (halive : state.alive id = true) (hread : state.readable id = true)
    (index : Nat) (hindex : index < a.cells.length) :
    readPacked state
      ⟨BitVec.ofNat 64 (backedPointer id a index).address,
        (backedPointer id a index).origin⟩ = some (a.cells[index]) := by
  have hb := a.noWrap
  have haddr : a.base + index * 16 < 2 ^ 64 := by omega
  have hptr : decodePointer
      ⟨BitVec.ofNat 64 (backedPointer id a index).address,
        (backedPointer id a index).origin⟩ = backedPointer id a index := by
    simp [decodePointer, backedPointer, BitVec.toNat_ofNat]
    exact haddr
  simp only [readPacked, backedPointer, Option.bind_some, halive, hread,
    Bool.true_and, if_true]
  change AspisV8R19.R432PointerPrimitive.read state.heap (decodePointer _) = _
  rw [hptr]
  exact read_backed state.heap id a hlookup index hindex

#print axioms readPacked
#print axioms acquireShared
#print axioms copyShared
#print axioms refSharedDeref
#print axioms copySharedDeref
#print axioms put_frame
#print axioms refSharedDeref_frame
#print axioms copySharedDeref_frame
#print axioms copy_acquired
#print axioms readPacked_backed
end AspisV8R19.R483SharedReadPlace
