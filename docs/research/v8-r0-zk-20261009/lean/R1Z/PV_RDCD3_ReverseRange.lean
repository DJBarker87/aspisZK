import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD3_ReverseRange
open Aeneas Aeneas.Std Result
abbrev Range := core.ops.range.Range Usize
abbrev Rev := core.iter.adapters.rev.Rev Range
def before (e : Usize) : Rev := ⟨⟨0#usize,e⟩⟩
def pred (e : Usize) : Usize :=
  Usize.ofNatCore (e.val-1) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) e.hBounds)
abbrev next (r : Rev) := core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) r

theorem pred_val (e : Usize) : (pred e).val=e.val-1 := rfl

theorem next_zero : next (before 0#usize)=.ok (none,before 0#usize) := by
  simp [next,before,
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize,core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.lt]

theorem next_pos (e : Usize) (positive : 0<e.val) :
    next (before e)=.ok (some (pred e),before (pred e)) := by
  have le : 1≤e.val := by omega
  simp [next,before,pred,
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize,core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.lt,core.iter.range.UScalarStep.backward_checked,
    positive,le]
  exact UScalar.eq_of_val_eq (by rfl)
#print axioms pred_val
#print axioms next_zero
#print axioms next_pos
end R1Z.PV_RDCD3_ReverseRange
