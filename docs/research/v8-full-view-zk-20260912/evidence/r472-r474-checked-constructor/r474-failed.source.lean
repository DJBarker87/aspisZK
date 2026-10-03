import AspisV8R19.R473SequenceRegrouping

/-! Generated syntactic projection of R440 constructor86. The generator checks
every supported native operation and operand and retains both branch arms.
This is not a certified JSON decoder or a Rust/LLBC memory-semantics theorem. -/
set_option autoImplicit false
namespace AspisV8R19.R474NativeConstructorProjection
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R433ConstructorFragment

def selected : Program :=
  .seq (.one (.live 0)) (.seq (.one (.live 5)) (.seq (.one (.live 2)) (.seq (.one (.metadata 2 1)) (.seq (.one (.live 3)) (.seq (.one (.live 4)) (.seq (.one (.live 8)) (.seq (.one (.rawSlice 8 1 1)) (.seq (.one (.cast 4 8 .sharedFatToNonNullFat)) (.seq (.one (.dead 8)) (.seq (.one (.live 9)) (.seq (.one (.live 10)) (.seq (.one (.cast 10 4 .nonNullFatToMutFat)) (.seq (.one (.cast 9 10 .mutFatToMutThin)) (.seq (.one (.dead 10)) (.seq (.one (.cast 3 9 .mutThinToNonNullThin)) (.seq (.one (.dead 9)) (.seq (.one (.dead 4)) (.seq (.globalIf 31 (.seq (.one (.cast 5 2 .wordToSharedThin)) (.nop)) (.seq (.one (.live 6)) (.seq (.one (.live 7)) (.seq (.one (.cast 7 3 .nonNullThinToMutThin)) (.seq (.one (.offset 6 7 2)) (.seq (.one (.dead 7)) (.seq (.one (.cast 5 6 .mutThinToSharedThin)) (.seq (.one (.dead 6)) (.nop))))))))) (.seq (.one (.live 11)) (.seq (.one (.marker 11)) (.seq (.one (.iterator 0 3 5 11)) (.seq (.one (.dead 3)) (.seq (.one (.dead 2)) (.seq (.one (.dead 5)) (.seq (.one (.dead 1)) (.seq (.one (.dead 11)) (.seq (.one .ret) (.nop))))))))))))))))))))))))))))

theorem execution_matches {T : Type} (heap : Heap T) (locals : Locals) :
    R472CheckedConstructor.program heap locals selected =
      R472CheckedConstructor.program heap locals constructor86 := by
  simp [selected, constructor86, R433ConstructorFragment.sequence,
    R473SequenceRegrouping.sequence_assoc, R473SequenceRegrouping.nop_left]

def execute {T : Type} (heap : Heap T) (ptr : Pointer)
    (length : Nat) : Option Iter := do
  let .returned (.iterator iter) _ ←
    R472CheckedConstructor.program heap (initial ptr length) selected | none
  some iter

theorem complete_checked_fragment {T : Type} (heap : Heap T)
    (ptr : Pointer) (length : Nat) (hptr : 0 < ptr.address) :
    execute heap ptr length = newIter heap ptr length := by
  unfold execute
  rw [execution_matches]
  exact R472CheckedConstructor.complete_constructor heap ptr length hptr

#print axioms selected
#print axioms execution_matches
#print axioms execute
#print axioms complete_checked_fragment
end AspisV8R19.R474NativeConstructorProjection
