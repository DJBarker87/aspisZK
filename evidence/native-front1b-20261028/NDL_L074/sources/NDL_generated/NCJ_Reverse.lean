import Aeneas
set_option autoImplicit false
namespace NCJ_Reverse
open Aeneas Aeneas.Std Result
abbrev Rev := core.iter.adapters.rev.Rev (core.ops.range.Range Usize)
abbrev next := core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)

def cursor (e : Usize) : Rev := ⟨⟨0#usize,e⟩⟩

theorem stop : next (cursor 0#usize)=ok (none,cursor 0#usize) := by
  simp only [next,cursor,core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize,core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,
    liftFun2,core.cmp.impls.PartialOrdUsize.lt]
  rfl

theorem step (e : Usize) (positive : 0< e.val) :
    ∃ i : Usize,i.val+1=e.val ∧ next (cursor e)=ok (some i,cursor i) := by
  simp only [next,cursor,core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize,core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,
    liftFun2,core.cmp.impls.PartialOrdUsize.lt,core.iter.range.UScalarStep.backward_checked]
  simp only [show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl]
  simp only [show decide (0< e.val)=true from decide_eq_true positive,bind_tc_ok,↓reduceIte,
    dif_pos (show 1≤ e.val by omega)]
  exact ⟨_,by simp;omega,rfl⟩

#print axioms stop
#print axioms step
end NCJ_Reverse
