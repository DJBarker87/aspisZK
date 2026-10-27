import RPu_FJa_InclusiveShape
set_option autoImplicit false
namespace AspisR1.FJa_InclusiveNext
open Aeneas Aeneas.Std Result
abbrev Range := core.ops.range.RangeInclusive Usize
abbrev next := core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepUsize
#print core.ops.range.RangeInclusive.is_empty
/-- Exhausted inclusive iterators cannot issue another callback. -/
theorem stop (s e : Usize) : next (⟨s,e,true⟩ : Range)=ok (none,⟨s,e,true⟩) := by
  simp [next,core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeInclusive.is_empty]
/-- The final included endpoint is visited once, then marked exhausted. -/
theorem last (e : Usize) : next (⟨e,e,false⟩ : Range)=ok (some e,⟨e,e,true⟩) := by
  simp [next,core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeInclusive.is_empty,core.iter.range.StepUsize,core.iter.range.UScalarStep,
    core.cmp.PartialOrdUsize,liftFun2,core.cmp.impls.PartialOrdUsize.lt,
    core.cmp.impls.PartialOrdUsize.le,core.clone.CloneUsize]
#print axioms stop
#print axioms last
end AspisR1.FJa_InclusiveNext
