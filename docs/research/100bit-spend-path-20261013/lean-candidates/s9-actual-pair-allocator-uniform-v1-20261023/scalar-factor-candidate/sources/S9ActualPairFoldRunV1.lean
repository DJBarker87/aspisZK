import AspisR1S9ProductionPairCutV1.Funs
import TransparentFoldRangeLawV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualPairFoldRunV1

theorem actual_fold_eq_range_run {B F : Type}
    (callback : core.ops.function.FnMut F (B × Usize) B)
    (range : core.ops.range.Range Usize) (initial : B) (closure : F) :
    AspisR1S9ProductionPairCutV1.core.iter.traits.iterator.Iterator.fold.default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      callback range initial closure =
      (do
        let (value,_) ← AspisR1S3S9RangeFoldP6.rangeFoldRun
          (range.end.val-range.start.val) range
          (AspisR1S9TransparentFoldRangeLawV1.foldStep callback) (initial,closure)
        ok value) := by
  have hsame :
      AspisR1S9ProductionPairCutV1.core.iter.traits.iterator.Iterator.fold.default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        callback range initial closure =
      AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        callback range initial closure := by rfl
  rw [hsame]
  exact AspisR1S9TransparentFoldRangeLawV1.extracted_fold_eq_rangeFoldRun callback range initial closure
#print axioms actual_fold_eq_range_run
end AspisR1S9ActualPairFoldRunV1
