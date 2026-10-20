import S4FromFnP6OuterSameClosureLoop0V1
import S4FromFnP6Loop0ArrayOpIrrelevanceV1
import FourDotsActualSevenBatchLimbBoundV2

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

/-- Apply the retained actual seven-batch arithmetic theorem to each of the
four source loop0 executions exposed by the same-q/g P6 trace. The only
operation-record transport is the proved fact that this loop does not read
`FourDotsOps.arrayFromFn`; P6 remains the explicit array-construction model. -/
theorem generatedFourDotsN4_success_four_actual_seven_batch_bounds
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (q : Aeneas.Std.Array Std.U8 608#usize)
    (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    {values : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 4#usize}
    (h : (fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 4#usize
      (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (fourDotsOpsWithP6ArrayFromFnN4N8
          (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) (q,g) = .ok values) :
    ∃ (v0 v1 v2 v3 : aspis_core.field.wide_exact.WideExact)
      (limbs0 limbs1 limbs2 limbs3 : Aeneas.Std.Array Std.U64 8#usize),
      (values.val = [v0,v1,v2,v3]) ∧
      (∀ i : Fin 8,
        AspisR1FastDotsActualSevenBatchLimbBoundV2.cell limbs0 i ≤
          7 * AspisR1FastDotsActualSevenBatchLimbBoundV2.Cap) ∧
      (∀ i : Fin 8,
        AspisR1FastDotsActualSevenBatchLimbBoundV2.cell limbs1 i ≤
          7 * AspisR1FastDotsActualSevenBatchLimbBoundV2.Cap) ∧
      (∀ i : Fin 8,
        AspisR1FastDotsActualSevenBatchLimbBoundV2.cell limbs2 i ≤
          7 * AspisR1FastDotsActualSevenBatchLimbBoundV2.Cap) ∧
      (∀ i : Fin 8,
        AspisR1FastDotsActualSevenBatchLimbBoundV2.cell limbs3 i ≤
          7 * AspisR1FastDotsActualSevenBatchLimbBoundV2.Cap) := by
  let actualOps := AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops
  obtain ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,vals0,vals1,vals2,vals3,
      hvalues,hcall0,hcall1,hcall2,hcall3,hstep,
      hloop0,harray0,hloop1,harray1,hloop2,harray2,hloop3,harray3⟩ :=
    generatedFourDotsN4_success_same_closure_loop0_four_calls actualOps q g h
  have hloop0' := hloop0
  have hloop1' := hloop1
  have hloop2' := hloop2
  have hloop3' := hloop3
  rw [generatedLoop0_ignores_p6_array_adapter actualOps _ q g 0#usize _] at hloop0'
  rw [generatedLoop0_ignores_p6_array_adapter actualOps _ q g 1#usize _] at hloop1'
  rw [generatedLoop0_ignores_p6_array_adapter actualOps _ q g 2#usize _] at hloop2'
  rw [generatedLoop0_ignores_p6_array_adapter actualOps _ q g 3#usize _] at hloop3'
  have hb0 := AspisR1FastDotsActualSevenBatchLimbBoundV2.actual_outer_startBy_success_seven_bound
    ops q g 0#usize limbs0 hcoords hloop0'
  have hb1 := AspisR1FastDotsActualSevenBatchLimbBoundV2.actual_outer_startBy_success_seven_bound
    ops q g 1#usize limbs1 hcoords hloop1'
  have hb2 := AspisR1FastDotsActualSevenBatchLimbBoundV2.actual_outer_startBy_success_seven_bound
    ops q g 2#usize limbs2 hcoords hloop2'
  have hb3 := AspisR1FastDotsActualSevenBatchLimbBoundV2.actual_outer_startBy_success_seven_bound
    ops q g 3#usize limbs3 hcoords hloop3'
  exact ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,hvalues,hb0,hb1,hb2,hb3⟩

#print axioms generatedFourDotsN4_success_four_actual_seven_batch_bounds

end AspisR1FromFnP6Generated
