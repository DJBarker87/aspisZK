import AspisV8R19.R433ConstructorFragment
import AspisV8R19.R470R440ReadonlyConstantGraph
import AspisV8R19.R471NonNullPointerValidity

/-! Complete constructor-fragment execution with checked NonNull conversions.
The R433 operation sequence is retained, including both branch arms and all
storage operations. R440's explicit readonly graph supplies the branch value.
This strengthens the proposed allocation interpretation; it does not assert
Rust/LLBC cast semantics or derive slice-reference validity from the caller.
None is fragment rejection, not an invented Rust error. -/
set_option autoImplicit false
namespace AspisV8R19.R472CheckedConstructor
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R433ConstructorFragment
open AspisV8R19.R471NonNullPointerValidity

def validCastResult : Value → Bool
  | .nonNullFat ptr _ => decide (0 < ptr.address)
  | .nonNullThin ptr => decide (0 < ptr.address)
  | _ => true

def checkedCast (kind : Cast) (value : Value) : Option Value := do
  let result ← castValue kind value
  if validCastResult result then some result else none

def command {T : Type} (heap : Heap T) (locals : Locals) :
    Command → Option Control
  | .cast dst src kind => do
      let value ← locals src
      let result ← checkedCast kind value
      some (.cont (put locals dst (some result)))
  | other => evalCommand heap locals other

def program {T : Type} (heap : Heap T) (locals : Locals) :
    Program → Option Control
  | .nop => some (.cont locals)
  | .one operation => command heap locals operation
  | .seq first second => do
      match ← program heap locals first with
      | .cont locals1 => program heap locals1 second
      | .returned value locals1 => some (.returned value locals1)
  | .globalIf id ifTrue ifFalse => do
      let .bool value ←
        AspisV8R19.R470R440ReadonlyConstantGraph.eval 7 (.global id) | none
      if value then program heap locals ifTrue
      else program heap locals ifFalse

def run {T : Type} (heap : Heap T) (ptr : Pointer)
    (length : Nat) : Option Iter := do
  let .returned (.iterator iter) _ ←
    program heap (initial ptr length) constructor86 | none
  some iter

theorem checked_fat_nonnull (ptr : Pointer) (length : Nat)
    (hptr : 0 < ptr.address) :
    checkedCast .sharedFatToNonNullFat (.rawFat .shared ptr length) =
      some (.nonNullFat ptr length) := by
  simp [checkedCast, castValue, validCastResult, hptr]

theorem checked_thin_nonnull (ptr : Pointer) (hptr : 0 < ptr.address) :
    checkedCast .mutThinToNonNullThin (.rawThin .mut ptr) =
      some (.nonNullThin ptr) := by
  simp [checkedCast, castValue, validCastResult, hptr]

theorem checked_fat_null (origin : Option (Nat × Nat)) (length : Nat) :
    checkedCast .sharedFatToNonNullFat
      (.rawFat .shared ⟨0, origin⟩ length) = none := by
  simp [checkedCast, castValue, validCastResult]

theorem checked_thin_null (origin : Option (Nat × Nat)) :
    checkedCast .mutThinToNonNullThin (.rawThin .mut ⟨0, origin⟩) = none := by
  simp [checkedCast, castValue, validCastResult]

theorem complete_constructor {T : Type} (heap : Heap T) (ptr : Pointer)
    (length : Nat) (hptr : 0 < ptr.address) :
    run heap ptr length = newIter heap ptr length := by
  have hglobal := AspisV8R19.R470R440ReadonlyConstantGraph.is_zst_global 0
  simp only [Nat.zero_add] at hglobal
  cases hAdd : add heap ptr length with
  | none =>
      simp [run, constructor86, R433ConstructorFragment.sequence, program, command, evalCommand,
        initial, put, checkedCast, castValue, validCastResult, hptr, hglobal,
        hAdd, newIter]
  | some last =>
      simp [run, constructor86, R433ConstructorFragment.sequence, program, command, evalCommand,
        initial, put, checkedCast, castValue, validCastResult, hptr, hglobal,
        hAdd, newIter]

theorem complete_null_rejection {T : Type} (heap : Heap T)
    (origin : Option (Nat × Nat)) (length : Nat) :
    run heap ⟨0, origin⟩ length = none := by
  simp [run, constructor86, R433ConstructorFragment.sequence, program, command, evalCommand,
    initial, put, checkedCast, castValue, validCastResult]

theorem complete_empty_dangling {T : Type} (heap : Heap T) (address : Nat)
    (haddress : 0 < address) :
    run heap ⟨address, none⟩ 0 =
      some ⟨⟨address, none⟩, ⟨address, none⟩⟩ := by
  rw [complete_constructor heap _ 0 haddress, newIter_empty]

theorem complete_backed {T : Type} (heap : Heap T) (id : Nat)
    (a : Allocation T) (hlookup : heap id = some a)
    (start length : Nat) (hbound : start + length ≤ a.cells.length) :
    run heap (backedPointer id a start) length =
      some ⟨backedPointer id a start, backedPointer id a (start + length)⟩ := by
  have hptr : 0 < (backedPointer id a start).address := by
    have h := a.nonzero
    simp only [backedPointer]
    omega
  rw [complete_constructor heap _ length hptr]
  exact newIter_backed heap id a hlookup start length hbound

theorem complete_endpoint_casts {T : Type} (heap : Heap T) (ptr : Pointer)
    (length : Nat) (iter : Iter) (hptr : 0 < ptr.address)
    (h : run heap ptr length = some iter) :
    (wrap iter.first).map unwrap = some iter.first ∧
    (wrap iter.last).map unwrap = some iter.last := by
  rw [complete_constructor heap ptr length hptr] at h
  exact iterator_casts_total heap ptr length iter hptr h

#print axioms validCastResult
#print axioms checkedCast
#print axioms command
#print axioms program
#print axioms run
#print axioms checked_fat_nonnull
#print axioms checked_thin_nonnull
#print axioms checked_fat_null
#print axioms checked_thin_null
#print axioms complete_constructor
#print axioms complete_null_rejection
#print axioms complete_empty_dangling
#print axioms complete_backed
#print axioms complete_endpoint_casts
end AspisV8R19.R472CheckedConstructor
