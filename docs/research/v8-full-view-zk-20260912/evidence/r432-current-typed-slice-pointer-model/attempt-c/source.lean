import AspisV8R19.R193CountedSliceFoldControl

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

theorem distance_backed {T : Type} (heap : Heap T) (id : Nat)
    (a : Allocation T) (hlookup : heap id = some a)
    (start length : Nat) (hbound : start + length ≤ a.cells.length) :
    unsignedDistance heap (backedPointer id a (start + length))
      (backedPointer id a start) = some length := by
  by_cases hzero : length = 0
  · subst length
    simp [unsignedDistance, backedPointer]
  · have hne : a.base + (start + length) * 16 ≠ a.base + start * 16 := by
      omega
    have hsub : (start + length) * 16 - start * 16 = length * 16 := by omega
    have hle : start * 16 ≤ (start + length) * 16 := by omega
    have hlast : (start + length) * 16 ≤ a.cells.length * 16 := by omega
    simp [unsignedDistance, backedPointer, hne, hlookup, hsub, hle, hlast]

def viewCells {T : Type} (a : Allocation T) (start length : Nat) : List T :=
  (a.cells.drop start).take length

theorem view_length {T : Type} (a : Allocation T)
    (start length : Nat) (hbound : start + length ≤ a.cells.length) :
    (viewCells a start length).length = length := by
  simp only [viewCells, List.length_take, List.length_drop]
  omega

theorem read_view {T : Type} (heap : Heap T) (id : Nat)
    (a : Allocation T) (hlookup : heap id = some a)
    (start length : Nat) (hbound : start + length ≤ a.cells.length)
    (index : Nat) (hindex : index < (viewCells a start length).length) :
    (add heap (backedPointer id a start) index).bind (read heap) =
      some ((viewCells a start length).get ⟨index, hindex⟩) := by
  have hi : index < length := by rw [view_length a start length hbound] at hindex; exact hindex
  have hiCells : start + index < a.cells.length := by omega
  rw [add_backed heap id a hlookup start index (by omega)]
  simp only [Option.bind_some]
  rw [read_backed heap id a hlookup (start + index) hiCells]
  congr 1
  simp [viewCells, List.get_eq_getElem, List.getElem_take, List.getElem_drop]

-- A totalization for the counted control model only. The unsupported result is
-- arbitrary; this is not a choice of Rust failure semantics. It is unreachable
-- for every in-bounds read in the theorem below.
def loadForControl {T : Type} (heap : Heap T) (ptr : Pointer)
    (unsupported : Aeneas.Std.Result T) (index : Nat) : Aeneas.Std.Result T :=
  match (add heap ptr index).bind (read heap) with
  | some value => .ok value
  | none => unsupported

theorem countedFold_pointer_view {T B F : Type}
    (heap : Heap T) (id : Nat) (a : Allocation T)
    (hlookup : heap id = some a) (start length : Nat)
    (hbound : start + length ≤ a.cells.length)
    (unsupported : Aeneas.Std.Result T)
    (k : Aeneas.Std.core.ops.function.FnMut F (B × T) B)
    (init : B) (f : F) :
    AspisV8R19.R193CountedSliceFoldControl.countedFold
      (loadForControl heap (backedPointer id a start) unsupported)
      length k init f = (do
        let (acc, _) ← AspisV8R19.R183DefaultFoldExecution.foldMutList
          k (viewCells a start length) f init
        Aeneas.Std.Result.ok acc) := by
  have h := AspisV8R19.R193CountedSliceFoldControl.countedFold_list
    (viewCells a start length) k f init
    (loadForControl heap (backedPointer id a start) unsupported)
    (by
      intro index hi
      simp [loadForControl, read_view heap id a hlookup start length hbound index hi])
  simpa only [view_length a start length hbound] using h

#print axioms add_zero
#print axioms newIter_empty
#print axioms equal_distance_zero
#print axioms add_backed
#print axioms newIter_backed
#print axioms backed_empty_iff
#print axioms read_backed
#print axioms offset_bytes_safe
#print axioms distance_backed
#print axioms view_length
#print axioms read_view
#print axioms countedFold_pointer_view
end AspisV8R19.R432PointerPrimitive
