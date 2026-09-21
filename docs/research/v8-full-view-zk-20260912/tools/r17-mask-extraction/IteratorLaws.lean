import AspisR17MaskSource.IteratorCompat

namespace AspisR17MaskSource.IteratorCompat
open Aeneas Aeneas.Std Result

theorem zipMutNext_some {T U : Type}
    (self : core.iter.adapters.zip.Zip (core.slice.iter.IterMut T)
      (alloc.vec.into_iter.IntoIter U))
    (x : T) (y : U) (a : core.slice.iter.IterMut T)
    (b : alloc.vec.into_iter.IntoIter U)
    (back : core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T)
    (ha : core.slice.iter.IteratorIterMut.next self.fst = ok (some x, a, back))
    (hb : alloc.vec.into_iter.IteratorIntoIter.next self.snd = ok (some y, b)) :
    zipMutNext self = ok (some (x, y), ⟨a, b⟩,
      fun current replacement =>
        { current with fst := back current.fst (replacement.map Prod.fst) }) := by
  simp [zipMutNext, ha, hb]

/-- Forward observations agree with the cached default Zip::next model.
This does not certify the Rust specialization or its allocator behavior. -/
theorem zipMutNext_forward {T U : Type}
    (self : core.iter.adapters.zip.Zip (core.slice.iter.IterMut T)
      (alloc.vec.into_iter.IntoIter U)) :
    (do let (value, iter, _) ← zipMutNext self; ok (value, iter)) =
      core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
        { next := iterMutNextForward }
        (core.iter.traits.iterator.IteratorVecIntoIter U) self := by
  cases ha : core.slice.iter.IteratorIterMut.next self.fst with
  | fail e => simp [zipMutNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
                    iterMutNextForward, ha]
  | div => simp [zipMutNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
                 iterMutNextForward, ha]
  | ok result =>
    rcases result with ⟨oa, a, back⟩
    cases oa with
    | none => simp [zipMutNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
                    iterMutNextForward, ha]
    | some x =>
      cases hb : alloc.vec.into_iter.IteratorIntoIter.next self.snd with
      | fail e => simp [zipMutNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
                        iterMutNextForward, ha, hb]
      | div => simp [zipMutNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
                     iterMutNextForward, ha, hb]
      | ok result =>
        rcases result with ⟨ob, b⟩
        cases ob <;>
          simp [zipMutNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
                iterMutNextForward, ha, hb]

#print axioms zipMutNext_some
#print axioms zipMutNext_forward
end AspisR17MaskSource.IteratorCompat
