import XRk_FunsExternal
open Aeneas Aeneas.Std Result ControlFlow Error
open XRk_Release
/- ABI models for the emitted mutable-iterator externals. P6 remains OPEN.
   Restoration is kept explicit rather than assumed by any top theorem. -/
def XRk_next {T : Type} (s : core.slice.iter.IterMut T) :
    Result (Option T × core.slice.iter.IterMut T) := do
  let (v, s, _) ← core.slice.iter.IteratorIterMut.next s
  ok (v,s)
def XRk_iterator (T : Type) : core.iter.traits.iterator.Iterator (core.slice.iter.IterMut T) T :=
  { next := XRk_next }
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.all
    {T F : Type} (f : core.ops.function.FnMut F T Bool)
    (s : core.slice.iter.IterMut T) (c : F) :
    Result (Bool × core.slice.iter.IterMut T × (core.slice.iter.IterMut T → core.slice.iter.IterMut T)) := do
  let (b,s) ← core.iter.traits.iterator.Iterator.all.default (XRk_iterator T) f s c
  ok (b,s,id)
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.enumerate
    {T : Type} (s : core.slice.iter.IterMut T) :
    Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T) ×
      (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T) → core.slice.iter.IterMut T)) :=
  ok (⟨s,0#usize⟩, fun r => r.iter)
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.step_by
    {T : Type} (s : core.slice.iter.IterMut T) (n : Usize) :
    Result (core.iter.adapters.step_by.StepBy (core.slice.iter.IterMut T) ×
      (core.iter.adapters.step_by.StepBy (core.slice.iter.IterMut T) → core.slice.iter.IterMut T)) := do
  let r ← core.iter.traits.iterator.Iterator.step_by.default s n
  ok (r,fun r => r.iter)
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.rev
    {T U : Type} (_ : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut T) U)
    (s : core.slice.iter.IterMut T) :
    Result (core.iter.adapters.rev.Rev (core.slice.iter.IterMut T) ×
      (core.iter.adapters.rev.Rev (core.slice.iter.IterMut T) → core.slice.iter.IterMut T)) :=
  ok (⟨s⟩,fun r => r.iter)
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.map
    {T U F : Type} (_ : core.ops.function.FnMut F T U)
    (s : core.slice.iter.IterMut T) (c : F) :
    Result (core.iter.adapters.map.Map (core.slice.iter.IterMut T) F ×
      (core.iter.adapters.map.Map (core.slice.iter.IterMut T) F → core.slice.iter.IterMut T)) :=
  ok (⟨s,c⟩,fun r => r.iter)
def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.collect
    {T B : Type} (f : core.iter.traits.collect.FromIterator B T)
    (s : core.slice.iter.IterMut T) : Result (B × core.slice.iter.IterMut T) := do
  let b ← core.iter.traits.iterator.Iterator.collect.default (XRk_iterator T) f s
  ok (b,s)
/- Reverse mutation preserves the original slice and writes back the selected
   last element. Source library next_back, slice/iter/macros.rs:438-452. -/
def core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back
    {T : Type} (s : core.slice.iter.IterMut T) :
    Result (Option T × core.slice.iter.IterMut T × (core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T)) := do
  let (v,r) ← core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back ⟨s.slice,0#usize⟩
  ok (v,{s with slice := r.slice},fun updated item =>
    match item with
    | none => updated
    | some x =>
      if h : (updated.slice.val ++ [x]).length ≤ Usize.max then
        {updated with slice := ⟨updated.slice.val ++ [x],h⟩}
      else s)

def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
    {B I F B1 T : Type} (it : core.iter.traits.iterator.Iterator I T)
    (fn : core.ops.function.FnMut F T B) (out : core.iter.traits.collect.FromIterator B1 B)
    (s : core.iter.adapters.map.Map I F) : Result B1 :=
  core.iter.traits.iterator.Iterator.collect.default
    { next := fun (s : core.iter.adapters.map.Map I F) => do
        let (v,i) ← it.next s.iter
        match v with
        | none => ok (none,{s with iter := i})
        | some v =>
          let (b,f) ← fn.call_mut s.f v
          ok (some b,⟨i,f⟩) } out s
