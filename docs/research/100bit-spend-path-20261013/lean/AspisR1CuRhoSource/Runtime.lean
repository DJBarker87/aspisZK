import CuSavingsIteratorBridge
import AspisR1CuRho.Funs

/-! A second interpretation of the unchanged finish declarations. At the
selected slice-iterator instance, next executes the emitted concrete standard
method, transporting only the identical two-field Enumerate layout. The
generic trait instance is not replaced outside this namespace. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CuRhoSource

abbrev field.QM31 := AspisR1CuRho.field.QM31
abbrev verifier.BatchedWeights := AspisR1CuRho.verifier.BatchedWeights
abbrev verifier.BatchedWeights.value := AspisR1CuRho.verifier.BatchedWeights.value
abbrev core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT :=
  AspisR1CuRho.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
abbrev core.iter.traits.iterator.Iterator.enumerate.trait_default :=
  @AspisR1CuRho.core.iter.traits.iterator.Iterator.enumerate.trait_default

def core.iter.adapters.enumerate.IteratorEnumerate.next {T : Type}
    (_selected : AspisR1CuRho.core.iter.traits.iterator.Iterator
      (Aeneas.Std.core.slice.iter.IterMut T) T)
    (input : Aeneas.Std.core.iter.adapters.enumerate.Enumerate
      (Aeneas.Std.core.slice.iter.IterMut T)) := do
  let (value,state,back) ← AspisR1.CuSavingsIteratorSource.next
    (AspisR1.CuSavingsIteratorBridge.fromStd input)
  Result.ok (value,AspisR1.CuSavingsIteratorBridge.toStd state,
    fun out replacement => AspisR1.CuSavingsIteratorBridge.toStd
      (back (AspisR1.CuSavingsIteratorBridge.fromStd out) replacement))

#print axioms core.iter.adapters.enumerate.IteratorEnumerate.next
end AspisR1CuRhoSource
