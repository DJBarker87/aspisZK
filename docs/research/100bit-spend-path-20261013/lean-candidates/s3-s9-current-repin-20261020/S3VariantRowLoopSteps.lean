import Aeneas.Std.RangeIter
import S3VariantRowAeneasCut

open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1.S3VariantRowAeneasCut

theorem row_loop_body_done
    (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize)
    (hge : iter.start.val ≥ iter.end.val) :
    row_loop_body j iter out = .ok (.done out) := by
  have hnot : ¬ iter.start.val < iter.end.val := by omega
  unfold row_loop_body
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.lt, liftFun2, hnot]

end AspisR1.S3VariantRowAeneasCut

#print axioms AspisR1.S3VariantRowAeneasCut.row_loop_body_done
