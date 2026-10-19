import Aeneas
import AspisR1CuRho.Types

/-! Namespace-local mutable Iterator interface for the emitted finish cone.
The ordinary Aeneas Iterator returns a pair; a borrowed item additionally needs
its mutable handback. This interface keeps that third component throughout
enumeration. It does not replace the global ordinary Iterator model.

The enumerate control flow follows the pinned core library: call inner next;
on Some, checked count increment and return the old count; on None, no count
increment. A returned copied index never changes the iterator state. Runtime
source admission and the consuming finish proof are separate obligations.
-/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CuRho

abbrev MutableEnumerate (I : Type) := Aeneas.Std.core.iter.adapters.enumerate.Enumerate I

structure core.iter.traits.iterator.Iterator (I Item : Type) where
  next : I → Result (Option Item × I × (I → Option Item → I))
  enumerate : I → Result (MutableEnumerate I × (MutableEnumerate I → I))

@[trait_default] def core.iter.traits.iterator.Iterator.enumerate.trait_default {I Item : Type}
    (_ : core.iter.traits.iterator.Iterator I Item) (iter : I) :
    Result (MutableEnumerate I × (MutableEnumerate I → I)) :=
  .ok ({iter := iter,count := 0#usize},fun out => out.iter)

def core.iter.adapters.enumerate.IteratorEnumerate.next {I Item : Type}
    (inst : core.iter.traits.iterator.Iterator I Item) (self : MutableEnumerate I) :
    Result (Option (Usize × Item) × MutableEnumerate I ×
      (MutableEnumerate I → Option (Usize × Item) → MutableEnumerate I)) := do
  let (value,iter,back) ← inst.next self.iter
  let handback : MutableEnumerate I → Option (Usize × Item) → MutableEnumerate I :=
    fun out item => {out with iter := back out.iter (item.map Prod.snd)}
  match value with
  | none => .ok (none,{self with iter := iter},handback)
  | some item =>
    let count ← UScalar.add self.count 1#usize
    .ok (some (self.count,item),{iter := iter,count := count},handback)

#print axioms core.iter.traits.iterator.Iterator.enumerate.trait_default
#print axioms core.iter.adapters.enumerate.IteratorEnumerate.next
end AspisR1CuRho
