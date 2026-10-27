import FJa_InclusiveNext
set_option autoImplicit false
namespace AspisR1.FJa_InclusiveSteps
open Aeneas Aeneas.Std Result
open FJa_InclusiveNext (next Range)
/-- Tiny iterator-control facts only, with no field values or recurrences. -/
theorem step2 : next (⟨2#usize,8#usize,false⟩ : Range)=ok (some 2#usize,⟨3#usize,8#usize,false⟩) := by
  have hb : 8 ≤ UScalar.max .Usize := by scalar_tac
  simp [next,core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeInclusive.is_empty,core.iter.range.StepUsize,core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,core.cmp.PartialOrdUsize,liftFun2,
    core.cmp.impls.PartialOrdUsize.lt,core.cmp.impls.PartialOrdUsize.le,
    show 3≤UScalar.max .Usize from by omega,show 4≤UScalar.max .Usize from by omega,
    show 5≤UScalar.max .Usize from by omega,show 6≤UScalar.max .Usize from by omega,
    show 7≤UScalar.max .Usize from by omega,hb]

theorem step3 : next (⟨3#usize,8#usize,false⟩ : Range)=ok (some 3#usize,⟨4#usize,8#usize,false⟩) := by
  have hb : 8 ≤ UScalar.max .Usize := by scalar_tac
  simp [next,core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeInclusive.is_empty,core.iter.range.StepUsize,core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,core.cmp.PartialOrdUsize,liftFun2,
    core.cmp.impls.PartialOrdUsize.lt,core.cmp.impls.PartialOrdUsize.le,
    show 3≤UScalar.max .Usize from by omega,show 4≤UScalar.max .Usize from by omega,
    show 5≤UScalar.max .Usize from by omega,show 6≤UScalar.max .Usize from by omega,
    show 7≤UScalar.max .Usize from by omega,hb]

theorem step4 : next (⟨4#usize,8#usize,false⟩ : Range)=ok (some 4#usize,⟨5#usize,8#usize,false⟩) := by
  have hb : 8 ≤ UScalar.max .Usize := by scalar_tac
  simp [next,core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeInclusive.is_empty,core.iter.range.StepUsize,core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,core.cmp.PartialOrdUsize,liftFun2,
    core.cmp.impls.PartialOrdUsize.lt,core.cmp.impls.PartialOrdUsize.le,
    show 3≤UScalar.max .Usize from by omega,show 4≤UScalar.max .Usize from by omega,
    show 5≤UScalar.max .Usize from by omega,show 6≤UScalar.max .Usize from by omega,
    show 7≤UScalar.max .Usize from by omega,hb]

theorem step5 : next (⟨5#usize,8#usize,false⟩ : Range)=ok (some 5#usize,⟨6#usize,8#usize,false⟩) := by
  have hb : 8 ≤ UScalar.max .Usize := by scalar_tac
  simp [next,core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeInclusive.is_empty,core.iter.range.StepUsize,core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,core.cmp.PartialOrdUsize,liftFun2,
    core.cmp.impls.PartialOrdUsize.lt,core.cmp.impls.PartialOrdUsize.le,
    show 3≤UScalar.max .Usize from by omega,show 4≤UScalar.max .Usize from by omega,
    show 5≤UScalar.max .Usize from by omega,show 6≤UScalar.max .Usize from by omega,
    show 7≤UScalar.max .Usize from by omega,hb]

theorem step6 : next (⟨6#usize,8#usize,false⟩ : Range)=ok (some 6#usize,⟨7#usize,8#usize,false⟩) := by
  have hb : 8 ≤ UScalar.max .Usize := by scalar_tac
  simp [next,core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeInclusive.is_empty,core.iter.range.StepUsize,core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,core.cmp.PartialOrdUsize,liftFun2,
    core.cmp.impls.PartialOrdUsize.lt,core.cmp.impls.PartialOrdUsize.le,
    show 3≤UScalar.max .Usize from by omega,show 4≤UScalar.max .Usize from by omega,
    show 5≤UScalar.max .Usize from by omega,show 6≤UScalar.max .Usize from by omega,
    show 7≤UScalar.max .Usize from by omega,hb]

theorem step7 : next (⟨7#usize,8#usize,false⟩ : Range)=ok (some 7#usize,⟨8#usize,8#usize,false⟩) := by
  have hb : 8 ≤ UScalar.max .Usize := by scalar_tac
  simp [next,core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.RangeInclusive.is_empty,core.iter.range.StepUsize,core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,core.cmp.PartialOrdUsize,liftFun2,
    core.cmp.impls.PartialOrdUsize.lt,core.cmp.impls.PartialOrdUsize.le,
    show 3≤UScalar.max .Usize from by omega,show 4≤UScalar.max .Usize from by omega,
    show 5≤UScalar.max .Usize from by omega,show 6≤UScalar.max .Usize from by omega,
    show 7≤UScalar.max .Usize from by omega,hb]

#print axioms step2
#print axioms step3
#print axioms step4
#print axioms step5
#print axioms step6
#print axioms step7
end AspisR1.FJa_InclusiveSteps
