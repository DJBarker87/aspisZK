import Aeneas.Std

/-! A proposed typed immutable allocation fragment for the selected 16-byte
QM31 layout. This does not supply Rust memory semantics, a source-validity
bridge, or a whole-fold contract. None denotes an unsupported/invalid fragment
operation, not a chosen Rust error. In particular, dangling empty slices are
retained and one-past arithmetic is distinct from element reads. -/
set_option autoImplicit false
namespace AspisV8R19.R432PointerPrimitive

structure Pointer where
  address : Nat
  origin : Option (Nat × Nat)
  deriving DecidableEq

structure Allocation (T : Type) where
  base : Nat
  cells : List T
  nonzero : 0 < base
  aligned : base % 4 = 0
  small : cells.length * 16 ≤ 2 ^ 63 - 1
  noWrap : base + cells.length * 16 < 2 ^ 64

abbrev Heap (T : Type) := Nat → Option (Allocation T)

def backedPointer {T : Type} (id : Nat) (a : Allocation T)
    (start : Nat) : Pointer :=
  ⟨a.base + start * 16, some (id, start * 16)⟩

-- Zero offset requires no live allocation, including for an empty slice.
def add {T : Type} (heap : Heap T) (ptr : Pointer)
    (count : Nat) : Option Pointer :=
  if count = 0 then some ptr else do
    let (id, offset) ← ptr.origin
    let a ← heap id
    if ptr.address = a.base + offset ∧
        offset + count * 16 ≤ a.cells.length * 16 then
      some ⟨ptr.address + count * 16, some (id, offset + count * 16)⟩
    else none

def read {T : Type} (heap : Heap T) (ptr : Pointer) : Option T := do
  let (id, offset) ← ptr.origin
  let a ← heap id
  if ptr.address = a.base + offset ∧ offset % 16 = 0 then
    a.cells[offset / 16]?
  else none

def eqAddress (left right : Pointer) : Bool :=
  decide (left.address = right.address)

-- Equal addresses are an explicit zero-distance case, even without allocation.
def unsignedDistance {T : Type} (heap : Heap T)
    (last first : Pointer) : Option Nat :=
  if last.address = first.address then some 0 else do
    let (idLast, offsetLast) ← last.origin
    let (idFirst, offsetFirst) ← first.origin
    let a ← heap idFirst
    if idLast = idFirst ∧ first.address = a.base + offsetFirst ∧
        last.address = a.base + offsetLast ∧
        offsetFirst ≤ offsetLast ∧ offsetLast ≤ a.cells.length * 16 ∧
        (offsetLast - offsetFirst) % 16 = 0 then
      some ((offsetLast - offsetFirst) / 16)
    else none

structure Iter where
  first : Pointer
  last : Pointer

def newIter {T : Type} (heap : Heap T) (ptr : Pointer)
    (length : Nat) : Option Iter := do
  let last ← add heap ptr length
  some ⟨ptr, last⟩

theorem add_zero {T : Type} (heap : Heap T) (ptr : Pointer) :
    add heap ptr 0 = some ptr := by simp [add]

theorem newIter_empty {T : Type} (heap : Heap T) (ptr : Pointer) :
    newIter heap ptr 0 = some ⟨ptr, ptr⟩ := by
  simp [newIter, add_zero]

theorem equal_distance_zero {T : Type} (heap : Heap T) (ptr : Pointer) :
    unsignedDistance heap ptr ptr = some 0 := by
  simp [unsignedDistance]

theorem add_backed {T : Type} (heap : Heap T) (id : Nat)
    (a : Allocation T) (hlookup : heap id = some a)
    (start count : Nat) (hbound : start + count ≤ a.cells.length) :
    add heap (backedPointer id a start) count =
      some (backedPointer id a (start + count)) := by
  by_cases hzero : count = 0
  · subst count
    simp [add_zero]
  · have hbytes : start * 16 + count * 16 ≤ a.cells.length * 16 := by omega
    simp [add, hzero, backedPointer, hlookup, hbytes, Nat.add_mul,
      Nat.add_assoc]

theorem newIter_backed {T : Type} (heap : Heap T) (id : Nat)
    (a : Allocation T) (hlookup : heap id = some a)
    (start length : Nat) (hbound : start + length ≤ a.cells.length) :
    newIter heap (backedPointer id a start) length =
      some ⟨backedPointer id a start, backedPointer id a (start + length)⟩ := by
  simp [newIter, add_backed heap id a hlookup start length hbound]

theorem backed_empty_iff {T : Type} (id : Nat) (a : Allocation T)
    (start length : Nat) :
    eqAddress (backedPointer id a start)
      (backedPointer id a (start + length)) = true ↔ length = 0 := by
  simp only [eqAddress, decide_eq_true_eq, backedPointer]
  omega

theorem read_backed {T : Type} (heap : Heap T) (id : Nat)
    (a : Allocation T) (hlookup : heap id = some a)
    (index : Nat) (hindex : index < a.cells.length) :
    read heap (backedPointer id a index) = some (a.cells[index]) := by
  simp [read, backedPointer, hlookup, Nat.mul_div_left,
    List.getElem?_eq_getElem hindex]

theorem offset_bytes_safe {T : Type} (a : Allocation T)
    (start count : Nat) (hbound : start + count ≤ a.cells.length) :
    count * 16 ≤ 2 ^ 63 - 1 ∧
    a.base + (start + count) * 16 < 2 ^ 64 ∧
    0 < a.base + (start + count) * 16 := by
  have hsmall := a.small
  have hnowrap := a.noWrap
  have hnonzero := a.nonzero
  omega

#print axioms add_zero
#print axioms newIter_empty
#print axioms equal_distance_zero
#print axioms add_backed
#print axioms newIter_backed
#print axioms backed_empty_iff
#print axioms read_backed
#print axioms offset_bytes_safe
end AspisV8R19.R432PointerPrimitive
