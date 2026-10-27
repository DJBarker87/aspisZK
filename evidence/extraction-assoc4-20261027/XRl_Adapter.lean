import XRk_ABI
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRl_Adapter
/-- The original stateful array::from_fn semantics: N sequential mutable calls,
followed by array construction. Unlike the fixed library ABI it retains F.
Rust sampler.rs:59-67 mutably captures quotient; fromFnList is the pinned
sequential library model, with its exact fail/div cases. -/
def originalFromFn {T F : Type} (N : Usize)
    (fn : core.ops.function.FnMut F Usize T) (c : F) : Result (Array T N × F) :=
  match core.array.fromFnList fn N.val 0#usize c with
  | .fail e => .fail e
  | .div => .div
  | .ok (xs,last) => if h : xs.length = N.val then .ok (⟨xs,h⟩,last) else .fail .panic

theorem fromFnState {T F : Type} (N : Usize)
    (fn : core.ops.function.FnMut F Usize T) (c : F) :
    XRk_fromFnState N fn c = originalFromFn N fn c := by
  unfold XRk_fromFnState originalFromFn
  cases core.array.fromFnList fn N.val 0#usize c with
  | fail e => rfl
  | div => rfl
  | ok r => rcases r with ⟨xs,last⟩; rfl

/-- The emitted array into_iter returns a backward function on the final
iterator state; the generated loop returns an endomorphism on its initial
state. This is their explicit composition, preserving the whole array. -/
def originalIntoIter {T : Type} {N : Usize} (a : Array T N) := do
  let (initial,back) ← MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter a
  ok (initial,fun (restore : core.slice.iter.IterMut T → core.slice.iter.IterMut T) => back (restore initial))
theorem intoIter {T : Type} {N : Usize} (a : Array T N) :
    XRk_intoIter a = originalIntoIter a := by rfl

/-- Original mutable rev construction followed by application of the emitted
restoration endomorphism before the original backward projection. -/
def originalRevRestored {T U : Type}
    (d : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut T) U)
    (s : core.slice.iter.IterMut T) := do
  let (r,back) ← core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.rev d s
  ok (r,fun (restore : core.iter.adapters.rev.Rev (core.slice.iter.IterMut T) → core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)) => back (restore r))
theorem revRestored {T U : Type}
    (d : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut T) U)
    (s : core.slice.iter.IterMut T) : XRk_revRestored d s = originalRevRestored d s := by rfl

def originalEnumerateRestored {T : Type} (s : core.slice.iter.IterMut T) := do
  let (r,back) ← core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.enumerate s
  ok (r,fun (restore : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T) → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)) => back (restore r))
theorem enumerateRestored {T : Type} (s : core.slice.iter.IterMut T) :
    XRk_enumerateRestored s = originalEnumerateRestored s := by rfl

/-- Original mutable Enumerate::next: number a yielded mutable borrow, advance
count only on Some, and write back the changed value without changing count.
The dictionary is fixed to the concrete mutable-slice iterator at the call site. -/
def originalEnumerateNext {T : Type}
    (s : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)) := do
  let (v,i,back) ← core.slice.iter.IteratorIterMut.next s.iter
  match v with
  | none => ok (none, (⟨i,s.count⟩ : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)),
      fun (r : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)) (item : Option (Usize × T)) => {r with iter := back r.iter (item.map Prod.snd)})
  | some x => do
    let n ← s.count + 1#usize
    ok (some (s.count,x), (⟨i,n⟩ : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)),
      fun (r : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)) (item : Option (Usize × T)) => {r with iter := back r.iter (item.map Prod.snd)})
theorem enumerateNext {T : Type}
    (d : core.iter.traits.iterator.Iterator (core.slice.iter.IterMut T) T)
    (s : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)) :
    XRk_enumerateNext d s = originalEnumerateNext s := by
  unfold XRk_enumerateNext originalEnumerateNext
  cases core.slice.iter.IteratorIterMut.next s.iter with
  | fail e => rfl
  | div => rfl
  | ok r =>
    rcases r with ⟨v,i,back⟩
    cases v <;> rfl

#print axioms fromFnState
#print axioms intoIter
#print axioms revRestored
#print axioms enumerateRestored
#print axioms enumerateNext
end XRl_Adapter
