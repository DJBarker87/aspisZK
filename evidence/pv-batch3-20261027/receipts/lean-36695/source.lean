import Aeneas.Std
namespace PV_B3_LinearsIterator
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Iter := core.iter.adapters.rev.Rev (core.ops.range.Range Usize)
def iter (n : Usize) : Iter := { iter := { start := 0#usize, «end» := n } }
def next (n : Usize) : Result (Option Usize × Iter) :=
  core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) (iter n)
#print core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
#print core.iter.range.IteratorRange.next_back
#print core.iter.range.StepUsize

theorem next_source (n : Usize) : next n =
    if 0#usize < n then
      ok (some (Usize.wrapping_sub n 1#usize), iter (Usize.wrapping_sub n 1#usize))
    else ok (none, iter n) := by
  simp only [next, iter, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator, core.iter.range.IteratorRange.next_back,
    core.iter.range.StepUsize]

#print axioms iter
#print axioms next
#print axioms next_source
end PV_B3_LinearsIterator
