import KSC2_MutCounterexamples
open Aeneas Aeneas.Std Result
namespace KSC2
-- Operation-local constructor transport. These laws do not certify any later
-- Iterator instance, callback, collect alias, or next_back implementation.
theorem mutable_enumerate_forward {T : Type} (s : core.slice.iter.IterMut T) :
    (do let (r,_) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.enumerate s
        ok r) = core.iter.traits.iterator.Iterator.enumerate.default s := rfl

theorem mutable_enumerate_restore {T : Type} (s : core.slice.iter.IterMut T)
    (updated : core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)) :
    (do let (_,restore) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.enumerate s
        ok (restore updated)) = ok updated.iter := rfl

theorem mutable_rev_forward {T U : Type}
    (d : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut T) U)
    (s : core.slice.iter.IterMut T) :
    (do let (r,_) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.rev d s
        ok r) = core.iter.traits.iterator.Iterator.rev.default s := rfl

theorem mutable_rev_restore {T U : Type}
    (d : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut T) U)
    (s : core.slice.iter.IterMut T)
    (updated : core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)) :
    (do let (_,restore) ← KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.rev d s
        ok (restore updated)) = ok updated.iter := rfl

theorem mutable_step_zero {T : Type} (s : core.slice.iter.IterMut T) :
    KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.step_by s 0#usize =
      fail .panic := rfl

theorem mutable_step_positive {T : Type} (s : core.slice.iter.IterMut T) (n : Usize)
    (hn : n.val ≠ 0) :
    KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.step_by s n =
      ok ((⟨s,n⟩ : core.iter.adapters.step_by.StepBy (core.slice.iter.IterMut T)),
        fun r => r.iter) := by
  simp only [KSA_Isolated.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.step_by,
    core.iter.traits.iterator.Iterator.step_by.default,hn,↓reduceIte,bind_tc_ok]

#print axioms mutable_enumerate_forward
#print axioms mutable_enumerate_restore
#print axioms mutable_rev_forward
#print axioms mutable_rev_restore
#print axioms mutable_step_zero
#print axioms mutable_step_positive
end KSC2
