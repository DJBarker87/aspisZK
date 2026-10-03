import AspisV8R19.R484BackedSharedReads

/-! Typed syntax projection of the two selected source assignments, interpreted
in R483's checked fragment. The external fail-closed LLBC projection is saved
with this target. Native input validity and the interpretation's Rust semantic
adequacy are separate, unproved obligations. -/
set_option autoImplicit false
namespace AspisV8R19.R485SelectedSharedRead
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R483SharedReadPlace
open AspisV8R19.R484BackedSharedReads
open AspisV8R19.R481NativeQM31Cell

inductive Place where
  | local (slot ty : Nat)
  | deref (base : Place) (ty : Nat)
  | unsupported

inductive Metadata where
  | unitAdt (ty : Nat)
  | unsupported

inductive Rvalue where
  | sharedRef (place : Place) (metadata : Metadata)
  | useCopy (place : Place) (copyYes : Bool)
  | unsupported

structure Assignment where
  destination : Place
  value : Rvalue

inductive Command where
  | acquire (dst src : Nat)
  | copy (dst src : Nat)

-- These type identifiers are pinned by the complete R440 source checksum.
-- No mismatched kind, place, metadata, type, or copy flag is accepted.
def decode (assignment : Assignment) : Option Command :=
  match assignment with
  | ⟨.local dst 4329, .sharedRef (.deref (.local src 4603) 544) (.unitAdt 891)⟩ =>
      some (.acquire dst src)
  | ⟨.local dst 544, .useCopy (.deref (.local src 5448) 544) true⟩ =>
      some (.copy dst src)
  | _ => none

def selectedAcquire : Assignment :=
  ⟨.local 20 4329, .sharedRef (.deref (.local 21 4603) 544) (.unitAdt 891)⟩

def selectedCopy : Assignment :=
  ⟨.local 9 544, .useCopy (.deref (.local 4 5448) 544) true⟩

def execute (state : State) (assignment : Assignment) : Outcome :=
  match decode assignment with
  | some (.acquire dst src) => refSharedDeref state dst src
  | some (.copy dst src) => copySharedDeref state dst src
  | none => .unsupported state

theorem decode_selectedAcquire : decode selectedAcquire = some (.acquire 20 21) := rfl
theorem decode_selectedCopy : decode selectedCopy = some (.copy 9 4) := rfl

theorem execute_frame (state : State) (assignment : Assignment) :
    frame state (execute state assignment).state := by
  unfold execute
  cases h : decode assignment with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some command =>
      cases command with
      | acquire dst src => exact refSharedDeref_frame state dst src
      | copy dst src => exact copySharedDeref_frame state dst src

theorem selectedAcquire_backed (state : State) (id : Nat)
    (a : Allocation (BitVec 128)) (hlookup : state.heap id = some a)
    (halive : state.alive id = true) (hread : state.readable id = true)
    (index : Nat) (hindex : index < a.cells.length)
    (hlocal : state.locals 21 = some (.rawMut (cellPointer id a index))) :
    execute state selectedAcquire = .supported
      (put state 20 (some (.shared (cellReference id a index)))) := by
  exact ref_statement_backed state id a hlookup halive hread index hindex 20 21 hlocal

theorem selectedCopy_backed (state : State) (id : Nat)
    (a : Allocation (BitVec 128)) (hlookup : state.heap id = some a)
    (halive : state.alive id = true) (hread : state.readable id = true)
    (index : Nat) (hindex : index < a.cells.length)
    (hlocal : state.locals 4 = some (.shared (cellReference id a index))) :
    execute state selectedCopy = .supported
      (put state 9 (some (.qm31 (decodeQM31 a.cells[index])))) := by
  exact copy_statement_backed state id a hlookup halive hread index hindex 9 4 hlocal

#print axioms decode
#print axioms execute
#print axioms decode_selectedAcquire
#print axioms decode_selectedCopy
#print axioms execute_frame
#print axioms selectedAcquire_backed
#print axioms selectedCopy_backed
end AspisV8R19.R485SelectedSharedRead
