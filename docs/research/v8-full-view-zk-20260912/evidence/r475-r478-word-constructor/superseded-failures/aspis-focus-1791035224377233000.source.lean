import AspisV8R19.R476WordConstructorExecution
import AspisV8R19.R474NativeConstructorProjection

/-! Complete word execution of the syntactically selected constructor fragment.
This composes explicit interpreters, not native Rust memory semantics. -/
set_option autoImplicit false
namespace AspisV8R19.R478SelectedWordConstructor
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R433ConstructorFragment
open AspisV8R19.R475PointerWordRuntime
open AspisV8R19.R476WordConstructorExecution

def wordInitial (ptr : WordPointer) (length : BitVec 64) : WordLocals :=
  fun index => if index = 1 then some (.sliceRef ptr length) else none

def decodeIter (iter : WordIter) : Iter :=
  ⟨decodePointer iter.first, decodePointer iter.last⟩

def run {T : Type} (heap : Heap T) (ptr : WordPointer)
    (length : BitVec 64) : Option WordIter := do
  let .returned (.iterator iter) _ ←
    program heap (wordInitial ptr length) R474NativeConstructorProjection.selected | none
  some iter

theorem initial_decode (ptr : WordPointer) (length : BitVec 64) :
    decodeLocals (wordInitial ptr length) = initial (decodePointer ptr) length.toNat := by
  funext index
  by_cases hi : index = 1 <;> simp [decodeLocals, wordInitial, initial, hi, decode]

theorem run_decode {T : Type} (heap : Heap T) (ptr : WordPointer)
    (length : BitVec 64) :
    (run heap ptr length).map decodeIter =
      R472CheckedConstructor.run heap (decodePointer ptr) length.toNat := by
  have hp := program_decode heap (wordInitial ptr length) R474NativeConstructorProjection.selected
  rw [initial_decode, R474NativeConstructorProjection.execution_matches] at hp
  cases hr : program heap (wordInitial ptr length) R474NativeConstructorProjection.selected with
  | none =>
      simp [hr] at hp
      simp [run, R472CheckedConstructor.run, hr, ← hp]
  | some result =>
      cases result with
      | cont locals =>
          simp [hr, decodeControl] at hp
          simp [run, R472CheckedConstructor.run, hr, ← hp]
      | returned value locals =>
          cases value <;> simp [hr, decodeControl, decode] at hp <;>
            simp [run, R472CheckedConstructor.run, hr, ← hp, decodeIter]

theorem complete_word_fragment {T : Type} (heap : Heap T) (ptr : WordPointer)
    (length : BitVec 64) (hptr : 0 < ptr.address.toNat) :
    (run heap ptr length).map decodeIter =
      newIter heap (decodePointer ptr) length.toNat := by
  rw [run_decode]
  exact R472CheckedConstructor.complete_constructor heap _ _ hptr

#print axioms wordInitial
#print axioms decodeIter
#print axioms run
#print axioms initial_decode
#print axioms run_decode
#print axioms complete_word_fragment
end AspisV8R19.R478SelectedWordConstructor
