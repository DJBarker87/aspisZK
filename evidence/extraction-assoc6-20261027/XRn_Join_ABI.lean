import XRn_Join_ByteFields
open Aeneas Aeneas.Std Result ControlFlow Error
open XRn_Join_Release
/- Explicit wrappers at the generated/library signature seams; P6 OPEN. -/
def XRn_Join_enumerateNext {T : Type}
    (_ : core.iter.traits.iterator.Iterator (core.slice.iter.IterMut T) T)
    (s : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)) :
    Result (Option (Usize × T) × core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T) ×
      (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T) → Option (Usize × T) →
        core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T))) := do
  let (v,i,restore) ← core.slice.iter.IteratorIterMut.next s.iter
  let n ← if v.isSome then s.count + 1#usize else ok s.count
  ok (v.map (s.count,·),⟨i,n⟩,fun r item => {r with iter := restore r.iter (item.map Prod.snd)})
def XRn_Join_reverseNext {T : Type}
    (_ : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut T) T)
    (s : core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)) :
    Result (Option T × core.iter.adapters.rev.Rev (core.slice.iter.IterMut T) ×
      (core.iter.adapters.rev.Rev (core.slice.iter.IterMut T) → core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)) ×
      (core.iter.adapters.rev.Rev (core.slice.iter.IterMut T) → Option T → core.iter.adapters.rev.Rev (core.slice.iter.IterMut T))) := do
  let (v,i,restore) ← core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back s.iter
  ok (v,⟨i⟩,fun r => ⟨restore r.iter v⟩,fun r item => ⟨restore r.iter item⟩)
def XRn_Join_nextBackPair {T : Type} (s : core.slice.iter.IterMut T) : Result (Option T × core.slice.iter.IterMut T) := do
  let (v,s,_) ← core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back s
  ok (v,s)
def XRn_Join_intoIter {T : Type} {N : Usize} (a : Array T N) :
    Result (core.slice.iter.IterMut T × ((core.slice.iter.IterMut T → core.slice.iter.IterMut T) → Array T N)) :=
  let s : core.slice.iter.IterMut T := {slice := a.to_slice}
  ok (s,fun restore => Array.from_slice a (restore s).slice)
def XRn_Join_fromFnState {T F : Type} (N : Usize)
    (fn : core.ops.function.FnMut F Usize T) (c : F) : Result (Array T N × F) := do
  let (xs,c) ← core.array.fromFnList fn N.val 0#usize c
  dite (xs.length = N.val) (fun h => ok (⟨xs,h⟩,c)) (fun _ => fail .panic)
def core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.any
    {T F : Type} (fn : core.ops.function.FnMut F (Slice T) Bool) :=
  core.iter.traits.iterator.Iterator.any.default {next := @core.slice.iter.IteratorChunksExact.next T} fn

def XRn_Join_revRestored {T U : Type}
    (d : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut T) U)
    (s : core.slice.iter.IterMut T) :
    Result (core.iter.adapters.rev.Rev (core.slice.iter.IterMut T) ×
      ((core.iter.adapters.rev.Rev (core.slice.iter.IterMut T) → core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)) → core.slice.iter.IterMut T)) := do
  let (r,back) ← core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.rev d s
  ok (r,fun restore => back (restore r))
def XRn_Join_enumerateRestored {T : Type} (s : core.slice.iter.IterMut T) :
    Result (core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T) ×
      ((core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T) → core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)) → core.slice.iter.IterMut T)) := do
  let (r,back) ← core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.enumerate s
  ok (r,fun restore => back (restore r))
