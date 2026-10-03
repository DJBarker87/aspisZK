import AspisV8R19.R430ReadonlyConstantGraph
import AspisV8R19.R432PointerPrimitive

/-! Proposed interpretation of the captured constructor's operation sequence.
This is a typed constant/pointer fragment with explicit primitive rules, not
Rust/LLBC memory semantics or a source lifetime/aliasing proof. Its source table
and constant-graph renaming must be checked before using it as source evidence.
Unsupported operations return None, not an invented Rust error. -/
set_option autoImplicit false
namespace AspisV8R19.R433ConstructorFragment
open AspisV8R19.R432PointerPrimitive

inductive Mutability where
  | shared | mut

inductive Value where
  | sliceRef (pointer : Pointer) (length : Nat)
  | rawFat (mutability : Mutability) (pointer : Pointer) (length : Nat)
  | nonNullFat (pointer : Pointer) (length : Nat)
  | rawThin (mutability : Mutability) (pointer : Pointer)
  | nonNullThin (pointer : Pointer)
  | word (value : Nat)
  | marker
  | iterator (value : Iter)

abbrev Locals := Nat → Option Value
def put (locals : Locals) (index : Nat) (value : Option Value) : Locals :=
  fun other => if other = index then value else locals other

inductive Cast where
  | sharedFatToNonNullFat
  | nonNullFatToMutFat
  | mutFatToMutThin
  | mutThinToNonNullThin
  | nonNullThinToMutThin
  | mutThinToSharedThin
  | wordToSharedThin

def castValue : Cast → Value → Option Value
  | .sharedFatToNonNullFat, .rawFat .shared ptr len => some (.nonNullFat ptr len)
  | .nonNullFatToMutFat, .nonNullFat ptr len => some (.rawFat .mut ptr len)
  | .mutFatToMutThin, .rawFat .mut ptr _ => some (.rawThin .mut ptr)
  | .mutThinToNonNullThin, .rawThin .mut ptr => some (.nonNullThin ptr)
  | .nonNullThinToMutThin, .nonNullThin ptr => some (.rawThin .mut ptr)
  | .mutThinToSharedThin, .rawThin .mut ptr => some (.rawThin .shared ptr)
  | .wordToSharedThin, .word len => some (.rawThin .shared ⟨len, none⟩)
  | _, _ => none

inductive Command where
  | live (index : Nat)
  | dead (index : Nat)
  | metadata (destination source : Nat)
  | rawSlice (destination source metadataSource : Nat)
  | cast (destination source : Nat) (kind : Cast)
  | offset (destination pointerSource countSource : Nat)
  | marker (destination : Nat)
  | iterator (destination pointerSource endSource markerSource : Nat)
  | ret

inductive Control where
  | cont (locals : Locals)
  | returned (value : Value) (locals : Locals)

def evalCommand {T : Type} (heap : Heap T) (locals : Locals) :
    Command → Option Control
  | .live index => some (.cont (put locals index none))
  | .dead index => some (.cont (put locals index none))
  | .metadata dst src => do
      let .sliceRef _ length ← locals src | none
      some (.cont (put locals dst (some (.word length))))
  | .rawSlice dst src metadataSource => do
      let .sliceRef ptr length ← locals src | none
      let .sliceRef _ metadataLength ← locals metadataSource | none
      if length = metadataLength then
        some (.cont (put locals dst (some (.rawFat .shared ptr length))))
      else none
  | .cast dst src kind => do
      let value ← locals src
      let value1 ← castValue kind value
      some (.cont (put locals dst (some value1)))
  | .offset dst pointerSource countSource => do
      let .rawThin .mut ptr ← locals pointerSource | none
      let .word count ← locals countSource | none
      let ptr1 ← add heap ptr count
      some (.cont (put locals dst (some (.rawThin .mut ptr1))))
  | .marker dst => some (.cont (put locals dst (some .marker)))
  | .iterator dst pointerSource endSource markerSource => do
      let .nonNullThin ptr ← locals pointerSource | none
      let .rawThin .shared last ← locals endSource | none
      let .marker ← locals markerSource | none
      -- The native aggregate copies its two pointer operands and moves marker11.
      let locals1 := put locals markerSource none
      some (.cont (put locals1 dst (some (.iterator ⟨ptr, last⟩))))
  | .ret => do
      let value ← locals 0
      some (.returned value locals)

inductive Program where
  | nop
  | one (command : Command)
  | seq (first second : Program)
  | globalIf (globalId : Nat) (ifTrue ifFalse : Program)

def sequence : List Command → Program
  | [] => .nop
  | command :: commands => .seq (.one command) (sequence commands)

def evalProgram {T : Type} (heap : Heap T) (locals : Locals) :
    Program → Option Control
  | .nop => some (.cont locals)
  | .one command => evalCommand heap locals command
  | .seq first second => do
      match ← evalProgram heap locals first with
      | .cont locals1 => evalProgram heap locals1 second
      | .returned value locals1 => some (.returned value locals1)
  | .globalIf globalId ifTrue ifFalse => do
      let .bool value ←
        AspisV8R19.R430ReadonlyConstantGraph.eval 7 (.global globalId) | none
      evalProgram heap locals (if value then ifTrue else ifFalse)

-- All 28 native top-level statements plus the two complete branch arms.
-- Return is an actual control result: a sequence cannot execute past it.
def constructor86 : Program :=
  .seq (sequence [
    .live 0, .live 5, .live 2, .metadata 2 1,
    .live 3, .live 4, .live 8, .rawSlice 8 1 1,
    .cast 4 8 .sharedFatToNonNullFat, .dead 8,
    .live 9, .live 10, .cast 10 4 .nonNullFatToMutFat,
    .cast 9 10 .mutFatToMutThin, .dead 10,
    .cast 3 9 .mutThinToNonNullThin, .dead 9, .dead 4])
  (.seq (.globalIf 31
    (sequence [.cast 5 2 .wordToSharedThin])
    (sequence [.live 6, .live 7, .cast 7 3 .nonNullThinToMutThin,
      .offset 6 7 2, .dead 7, .cast 5 6 .mutThinToSharedThin, .dead 6]))
    (sequence [.live 11, .marker 11, .iterator 0 3 5 11,
      .dead 3, .dead 2, .dead 5, .dead 1, .dead 11, .ret]))

def initial (ptr : Pointer) (length : Nat) : Locals :=
  put (fun _ => none) 1 (some (.sliceRef ptr length))

def runConstructor {T : Type} (heap : Heap T) (ptr : Pointer)
    (length : Nat) : Option Iter := do
  let .returned (.iterator iter) _ ←
    evalProgram heap (initial ptr length) constructor86 | none
  some iter

theorem constructor_fragment {T : Type} (heap : Heap T) (ptr : Pointer)
    (length : Nat) :
    runConstructor heap ptr length = newIter heap ptr length := by
  have hglobal := AspisV8R19.R430ReadonlyConstantGraph.is_zst_global 0
  simp only [Nat.zero_add] at hglobal
  cases hAdd : add heap ptr length with
  | none =>
      simp [runConstructor, constructor86, sequence, evalProgram, evalCommand,
        initial, put, castValue, hglobal, hAdd, newIter]
  | some last =>
      simp [runConstructor, constructor86, sequence, evalProgram, evalCommand,
        initial, put, castValue, hglobal, hAdd, newIter]

theorem constructor_empty {T : Type} (heap : Heap T) (ptr : Pointer) :
    runConstructor heap ptr 0 = some ⟨ptr, ptr⟩ := by
  rw [constructor_fragment, newIter_empty]

theorem constructor_backed {T : Type} (heap : Heap T) (id : Nat)
    (a : Allocation T) (hlookup : heap id = some a)
    (start length : Nat) (hbound : start + length ≤ a.cells.length) :
    runConstructor heap (backedPointer id a start) length =
      some ⟨backedPointer id a start, backedPointer id a (start + length)⟩ := by
  rw [constructor_fragment, newIter_backed heap id a hlookup start length hbound]

#print axioms constructor86
#print axioms constructor_fragment
#print axioms constructor_empty
#print axioms constructor_backed
end AspisV8R19.R433ConstructorFragment
