import RPt_JFs_TX2_Inner
set_option autoImplicit false
namespace AspisR1.JFs_TX2_Iterator
open Aeneas Aeneas.Std Result
abbrev Iter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

def cursor (k : Fin 8) : Usize := Usize.ofNat (min (4*k.val) 26) (by have:=k.isLt;scalar_tac)
def value (k : Fin 8) : Iter := ⟨{start:=cursor k,«end»:=26#usize},4#usize⟩

theorem next (iter : Iter) (hstep : iter.step_by.val=4)
    (active : iter.iter.start.val < iter.iter.end.val) :
    ∃ next, core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter=
        ok (some iter.iter.start,next) ∧
      next.iter.start.val=min (iter.iter.start.val+4) iter.iter.end.val ∧
      next.iter.end=iter.iter.end ∧ next.step_by.val=4 := by
  obtain ⟨⟨o,next⟩,run,post⟩ := WP.spec_imp_exists
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter (by omega))
  dsimp only [WP.uncurry'] at post
  rw [if_pos active] at post
  rw [post.1.1] at run
  exact ⟨next,run,by simpa only [hstep] using post.1.2,post.2.1,
    (congrArg UScalar.val post.2.2).trans hstep⟩

theorem stopped (iter : Iter) (stop : iter.iter.end.val≤ iter.iter.start.val) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter=ok (none,iter) := by
  obtain ⟨⟨o,next⟩,run,post⟩ := WP.spec_imp_exists
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec iter stop)
  dsimp only [WP.uncurry'] at post
  rw [post.1,post.2] at run
  exact run

theorem done : core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) (value 7)=ok (none,value 7) := by rfl

theorem initial : core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      {start:=0#usize,«end»:=26#usize} 4#usize=ok (value 0) := by rfl

theorem start (k : Fin 7) : (cursor ⟨k.val,by have:=k.isLt;omega⟩).val=4*k.val := by
  unfold cursor
  have h:=k.isLt
  scalar_tac

#print axioms next
#print axioms stopped
#print axioms done
#print axioms initial
#print axioms start
end AspisR1.JFs_TX2_Iterator
