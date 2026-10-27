import KSA_XRn_Join_ABI
open Aeneas Aeneas.Std Result
namespace KSC2
theorem range_collect {A B : Type} (step : core.iter.range.Step A) (out : core.iter.traits.collect.FromIterator B A) (s : core.ops.range.Range A) :
    KSA_Isolated.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.collect step out s =
      core.iter.traits.iterator.Iterator.collect.default (core.iter.traits.iterator.IteratorRange step) out s := rfl
#print axioms range_collect

theorem range_rev {A U : Type} (step : core.iter.range.Step A) (d : core.iter.traits.double_ended.DoubleEndedIterator (core.ops.range.Range A) U) (s : core.ops.range.Range A) :
    KSA_Isolated.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.rev step d s =
      core.iter.traits.iterator.Iterator.rev.default s := rfl
#print axioms range_rev

theorem range_enumerate {A : Type} (step : core.iter.range.Step A) (s : core.ops.range.Range A) :
    KSA_Isolated.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.enumerate step s =
      core.iter.traits.iterator.Iterator.enumerate.default s := rfl
#print axioms range_enumerate

theorem range_step_by {A : Type} (step : core.iter.range.Step A) (s : core.ops.range.Range A) (n : Usize) :
    KSA_Isolated.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.step_by step s n =
      core.iter.traits.iterator.Iterator.step_by.default s n := rfl
#print axioms range_step_by

theorem iter_collect {T B : Type} (out : core.iter.traits.collect.FromIterator B T) (s : core.slice.iter.Iter T) :
    KSA_Isolated.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.collect out s =
      core.iter.traits.iterator.Iterator.collect.default (core.iter.traits.iterator.IteratorSliceIter T) out s := rfl
#print axioms iter_collect

theorem iter_rev {T U : Type} (d : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.Iter T) U) (s : core.slice.iter.Iter T) :
    KSA_Isolated.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rev d s =
      core.iter.traits.iterator.Iterator.rev.default s := rfl
#print axioms iter_rev

theorem iter_enumerate {T : Type} (s : core.slice.iter.Iter T) :
    KSA_Isolated.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.enumerate s =
      core.iter.traits.iterator.Iterator.enumerate.default s := rfl
#print axioms iter_enumerate

theorem iter_step_by {T : Type} (s : core.slice.iter.Iter T) (n : Usize) :
    KSA_Isolated.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.step_by s n =
      core.iter.traits.iterator.Iterator.step_by.default s n := rfl
#print axioms iter_step_by

end KSC2
