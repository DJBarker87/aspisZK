import V6OuterLoopSuccessTransferV1
import FourDotsActualSevenBatchLimbBoundV2

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsV6OuterSevenBatchBoundV1

abbrev Ops := AspisR1FastDotsActualBatchLimbBoundV1.Ops
abbrev Usize := Std.Usize
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsActualBatchLimbBoundV1.Wide
abbrev NewLoop := AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0
abbrev NewOps := AspisR1FastDotsV6OuterLoopSuccessTransferV1.NewOps

/-- The v6 fixed-arithmetic outer loop inherits the retained exact seven-batch
    limb bound by success transfer to the original emitted outer loop. -/
theorem v6_outer_startBy_success_seven_bound
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (out : Array U64 8#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    (hnew : NewLoop (NewOps ops) AspisR1FastDotsStepSchedule.startBy a g slot
      (Array.repeat 8#usize 0#u64) = .ok out) :
    ∀ i : Fin 8,
      AspisR1FastDotsActualSevenBatchLimbBoundV2.cell out i ≤
        7 * AspisR1FastDotsActualSevenBatchLimbBoundV2.Cap := by
  apply AspisR1FastDotsActualSevenBatchLimbBoundV2.actual_outer_startBy_success_seven_bound
    ops a g slot out hcoords
  exact AspisR1FastDotsV6OuterLoopSuccessTransferV1.v6_outer_loop_success_old_loop
    ops a g slot AspisR1FastDotsStepSchedule.startBy (Array.repeat 8#usize 0#u64)
    out (by norm_num [AspisR1FastDotsStepSchedule.startBy,
      AspisR1FastDotsStepSchedule.startRange]) (by rfl) hnew

#print axioms v6_outer_startBy_success_seven_bound

end AspisR1FastDotsV6OuterSevenBatchBoundV1
