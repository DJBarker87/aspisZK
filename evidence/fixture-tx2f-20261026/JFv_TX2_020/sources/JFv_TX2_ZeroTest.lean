import Port4C_GeometryStd
set_option autoImplicit false
namespace AspisR1.JFv_TX2_ZeroTest
open Aeneas Aeneas.Std Result

theorem source {T : Type} (pred : core.ops.function.FnMut Unit T Bool)
    (it : core.slice.iter.Iter T) (fuel : Nat)
    (remaining : it.i+fuel=it.slice.val.length)
    (falseCalls : ∀ j (hj : j< it.slice.val.length), it.i≤j →
      pred.call_mut () it.slice.val[j]=ok (false,())) :
    Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter T) pred it ()=
      ok (false,{it with i:=it.slice.val.length}) := by
  induction fuel generalizing it with
  | zero =>
    have next : core.slice.iter.IteratorSliceIter.next it=ok (none,it) := by
      unfold core.slice.iter.IteratorSliceIter.next
      split
      · rename_i active
        change it.i < it.slice.val.length at active
        omega
      · rfl
    unfold Port3_BatchStd.anyDefault
    rw [Aeneas.Std.loop.eq_def]
    simp only [Port3_BatchStd.anyBody,core.iter.traits.iterator.IteratorSliceIter,
      next,bind_tc_ok]
    have hi : it.i=it.slice.val.length := by omega
    cases it
    simp_all
  | succ fuel ih =>
    have active : it.i< it.slice.val.length := by omega
    have step := falseCalls it.i active (Nat.le_refl _)
    have tail := ih {it with i:=it.i+1} (by simp;omega)
      (by intro j hj lo;exact falseCalls j hj (by simp at lo;omega))
    have next : core.slice.iter.IteratorSliceIter.next it=
        ok (some it.slice.val[it.i],{it with i:=it.i+1}) := by
      unfold core.slice.iter.IteratorSliceIter.next
      split
      · rfl
      · rename_i bad;exact False.elim (bad active)
    unfold Port3_BatchStd.anyDefault
    rw [Aeneas.Std.loop.eq_def]
    simp only [Port3_BatchStd.anyBody,core.iter.traits.iterator.IteratorSliceIter,
      next,bind_tc_ok,step,Bool.false_eq_true,if_false]
    exact tail
#print axioms source
end AspisR1.JFv_TX2_ZeroTest
