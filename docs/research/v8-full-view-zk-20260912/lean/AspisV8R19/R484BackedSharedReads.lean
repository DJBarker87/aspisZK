import AspisV8R19.R483SharedReadPlace

/-! Focused initialized-cell proof for the checked shared-read fragment.
The native caller's allocation image and access permissions are still explicit
premises; this file does not establish them from Rust execution. -/
set_option autoImplicit false
namespace AspisV8R19.R484BackedSharedReads
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R475PointerWordRuntime
open AspisV8R19.R481NativeQM31Cell
open AspisV8R19.R483SharedReadPlace

def cellPointer (id : Nat) (a : Allocation (BitVec 128)) (index : Nat) : WordPointer :=
  ⟨BitVec.ofNat 64 (backedPointer id a index).address,
    (backedPointer id a index).origin⟩

def cellReference (id : Nat) (a : Allocation (BitVec 128)) (index : Nat) : SharedRef :=
  ⟨cellPointer id a index, id⟩

theorem acquire_backed (state : State) (id : Nat)
    (a : Allocation (BitVec 128)) (hlookup : state.heap id = some a)
    (halive : state.alive id = true) (hread : state.readable id = true)
    (index : Nat) (hindex : index < a.cells.length) :
    acquireShared state (cellPointer id a index) = some (cellReference id a index) := by
  have hr := readPacked_backed state id a hlookup halive hread index hindex
  change readPacked state (cellPointer id a index) = some (a.cells[index]) at hr
  simp only [cellPointer, backedPointer] at hr
  simp [acquireShared, cellPointer, cellReference, backedPointer, hr]

theorem copy_backed (state : State) (id : Nat)
    (a : Allocation (BitVec 128)) (hlookup : state.heap id = some a)
    (halive : state.alive id = true) (hread : state.readable id = true)
    (index : Nat) (hindex : index < a.cells.length) :
    copyShared state (cellReference id a index) = some (decodeQM31 a.cells[index]) := by
  rw [copy_acquired state (cellPointer id a index) (cellReference id a index)
    (acquire_backed state id a hlookup halive hread index hindex)]
  rw [show readPacked state (cellPointer id a index) = some (a.cells[index]) from
    readPacked_backed state id a hlookup halive hread index hindex]
  rfl

theorem ref_statement_backed (state : State) (id : Nat)
    (a : Allocation (BitVec 128)) (hlookup : state.heap id = some a)
    (halive : state.alive id = true) (hread : state.readable id = true)
    (index : Nat) (hindex : index < a.cells.length) (dst src : Nat)
    (hlocal : state.locals src = some (.rawMut (cellPointer id a index))) :
    refSharedDeref state dst src = .supported
      (put state dst (some (.shared (cellReference id a index)))) := by
  simp [refSharedDeref, hlocal,
    acquire_backed state id a hlookup halive hread index hindex]

theorem copy_statement_backed (state : State) (id : Nat)
    (a : Allocation (BitVec 128)) (hlookup : state.heap id = some a)
    (halive : state.alive id = true) (hread : state.readable id = true)
    (index : Nat) (hindex : index < a.cells.length) (dst src : Nat)
    (hlocal : state.locals src = some (.shared (cellReference id a index))) :
    copySharedDeref state dst src = .supported
      (put state dst (some (.qm31 (decodeQM31 a.cells[index])))) := by
  simp [copySharedDeref, hlocal,
    copy_backed state id a hlookup halive hread index hindex]

theorem put_other_local (state : State) (dst slot : Nat) (value : Option Value)
    (h : slot ≠ dst) : (put state dst value).locals slot = state.locals slot := by
  simp [put, h]

-- Acquisition only changes the destination local. The same initialized cell
-- is copied without re-assuming either its value or a successful second read.
theorem acquired_copy_after_put (state : State) (id : Nat)
    (a : Allocation (BitVec 128)) (hlookup : state.heap id = some a)
    (halive : state.alive id = true) (hread : state.readable id = true)
    (index : Nat) (hindex : index < a.cells.length) (dst : Nat) :
    copyShared (put state dst (some (.shared (cellReference id a index))))
      (cellReference id a index) = some (decodeQM31 a.cells[index]) := by
  exact copy_backed (put state dst (some (.shared (cellReference id a index))))
    id a hlookup halive hread index hindex

#print axioms cellPointer
#print axioms cellReference
#print axioms acquire_backed
#print axioms copy_backed
#print axioms ref_statement_backed
#print axioms copy_statement_backed
#print axioms put_other_local
#print axioms acquired_copy_after_put
end AspisV8R19.R484BackedSharedReads
