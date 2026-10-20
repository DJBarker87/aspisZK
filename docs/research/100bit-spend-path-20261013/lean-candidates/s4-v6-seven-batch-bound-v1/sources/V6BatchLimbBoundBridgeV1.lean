import NewOuterLimbLoopSegmentV1
import FourDotsActualBatchLimbBoundV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsV6BatchLimbBoundBridgeV1

abbrev Ops := AspisR1FastDotsActualBatchLimbBoundV1.Ops
abbrev Usize := Std.Usize
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev StepBy := AspisR1FastDotsActualBatchLimbBoundV1.StepBy
abbrev cap := AspisR1FastDotsActualLimbFoldBodyFacadeV2.limbCap
abbrev cell := AspisR1FastDotsActualLimbFoldBodyFacadeV2.cell

/-- Transfer a successful v6 fixed arithmetic batch body into the retained
    emitted batch bound theorem. The same ops object is used on both bodies. -/
theorem v6_batch_body_success_limb_bound
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter iter' : StepBy)
    (limbs limbs' : Array U64 8#usize) (batchCount : Nat)
    (houterEnd : iter.iter.end.val = 26)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    (hstep : iter.step_by = 4#usize)
    (hinput : ∀ i : Fin 8, cell limbs i ≤ batchCount * cap)
    (hbody :
      AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0.body
        (AspisR1FastDotsActualBatchLimbBoundV1.BatchTermsOps
          (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
        q g slot iter limbs = .ok (.cont (iter', limbs'))) :
    ∀ i : Fin 8, cell limbs' i ≤ (batchCount + 1) * cap := by
  let boundOps := AspisR1FastDotsActualBatchLimbBoundV1.BatchTermsOps
    (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)
  have hcount : boundOps.wideLimbCount = .ok 8#usize := rfl
  have htransferred :=
    AspisR1FastDotsNewOuterLimbLoopSegmentV1.fixed_batch_body_success_old_body
      boundOps q g slot iter iter' limbs limbs' hcount hbody
  exact AspisR1FastDotsActualBatchLimbBoundV1.batch_body_success_limb_bound
    ops q g slot iter iter' limbs limbs' batchCount houterEnd hcoords hstep hinput
    htransferred

#print axioms v6_batch_body_success_limb_bound

end AspisR1FastDotsV6BatchLimbBoundBridgeV1
