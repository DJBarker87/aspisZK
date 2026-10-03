import AspisV8R19.R472CheckedConstructor

/-! Regrouping preserves every fragment result, early return, rejection and
local state. These are interpreter laws, not a Rust/LLBC semantics theorem. -/
set_option autoImplicit false
namespace AspisV8R19.R473SequenceRegrouping
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R433ConstructorFragment
open AspisV8R19.R472CheckedConstructor

theorem sequence_assoc {T : Type} (heap : Heap T) (locals : Locals)
    (first second third : Program) :
    program heap locals (.seq (.seq first second) third) =
      program heap locals (.seq first (.seq second third)) := by
  cases hf : program heap locals first with
  | none => simp [program, hf]
  | some result =>
      cases result with
      | returned value state => simp [program, hf]
      | cont state =>
          cases hs : program heap state second with
          | none => simp [program, hf, hs]
          | some result => cases result <;> simp [program, hf, hs]

theorem nop_left {T : Type} (heap : Heap T) (locals : Locals)
    (next : Program) :
    program heap locals (.seq .nop next) = program heap locals next := by
  simp [program]

theorem nop_right {T : Type} (heap : Heap T) (locals : Locals)
    (first : Program) :
    program heap locals (.seq first .nop) = program heap locals first := by
  cases hf : program heap locals first with
  | none => simp [program, hf]
  | some result => cases result <;> simp [program, hf]

def append : Program → Program → Program
  | .nop, next => next
  | .seq first second, next => append first (append second next)
  | first, next => .seq first next

theorem append_execution {T : Type} (heap : Heap T) (first next : Program)
    (locals : Locals) :
    program heap locals (append first next) =
      program heap locals (.seq first next) := by
  induction first generalizing next locals with
  | nop => simp [append, nop_left]
  | one operation => rfl
  | globalIf id yes no ihYes ihNo => rfl
  | seq first second ihFirst ihSecond =>
      simp only [append, ihFirst]
      rw [sequence_assoc]
      simp only [program, ihSecond]

def normalize : Program → Program
  | .seq first second => append (normalize first) (normalize second)
  | .globalIf id yes no => .globalIf id (normalize yes) (normalize no)
  | other => other

theorem normalize_execution {T : Type} (heap : Heap T) (source : Program)
    (locals : Locals) :
    program heap locals (normalize source) = program heap locals source := by
  induction source generalizing locals with
  | nop => rfl
  | one operation => rfl
  | seq first second ihFirst ihSecond =>
      simp only [normalize, append_execution, program, ihFirst, ihSecond]
  | globalIf id yes no ihYes ihNo =>
      simp only [normalize, program, ihYes, ihNo]

#print axioms sequence_assoc
#print axioms nop_left
#print axioms nop_right
#print axioms append
#print axioms append_execution
#print axioms normalize
#print axioms normalize_execution
end AspisV8R19.R473SequenceRegrouping
