import S3VariantRowAeneasCut

open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1.S3VariantRowAeneasCut

theorem s2_row_result_total (j : Std.Usize) :
    ∃ out, s2_row_result j = .ok out := by
  simp [s2_row_result, row_loop, Aeneas.Std.loop, row_loop_body, tau,
    core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.lt, liftFun2]

end AspisR1.S3VariantRowAeneasCut

#print axioms AspisR1.S3VariantRowAeneasCut.s2_row_result_total
