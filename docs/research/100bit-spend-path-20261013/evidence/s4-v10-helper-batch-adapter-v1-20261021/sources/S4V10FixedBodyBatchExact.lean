import FourDotsActualBatchExactRootV1
import NewOuterLimbLoopSegmentV1
import AspisR1FastDotsCurrent.FunsOpsFixedV6

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsV10FixedBodyBatchExact

open AspisR1FastDotsActualTermTraceRootV1

abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev ActualOps := AspisR1FastDotsActualBatchExactRootV1.actualOps
abbrev FixedBody := AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0.body

/-- The v10 extracted helper body is pinned byte-for-byte to the v6 fixed-call
    body by the source checker.  This operation-parameterized Lean theorem then
    transports a successful fixed body through the already-proved eight-step
    old-body bridge and consumes the actual batch theorem.  It leaves the Rust
    `from_fn`/Try-trait boundary and the v10 FunsExternal template unclaimed. -/
theorem v10_fixed_body_success_actual_batch_exact
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (iter it' : StepBy) (limbs limbs' : Array U64 8#usize)
    (houterEnd : iter.iter.end.val = 26)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (hstep : iter.step_by = 4#usize)
    (hbody : FixedBody (ActualOps ops) a a1 slot iter limbs =
      .ok (.cont (it', limbs'))) :
    ∃ (start batchEndArg rangeEnd : Usize) (sums : Array U64 8#usize)
      (cs : List Contribution),
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (some start,it') ∧
      UScalar.add start 4#usize = .ok batchEndArg ∧
      core.cmp.min core.cmp.OrdUsize batchEndArg 26#usize = .ok rangeEnd ∧
      TermLoop (ActualOps ops)
        {start, «end» := rangeEnd} a a1 slot (Array.repeat 8#usize 0#u64) = .ok sums ∧
      ActualTermTrace (ActualOps ops)
        a a1 slot {start, «end» := rangeEnd}
        (Array.repeat 8#usize 0#u64) sums cs ∧
      cs.length ≤ 4 ∧
      (∀ c ∈ cs, ∀ j : Fin 8, c.product j ≤
        cap) ∧
      ∀ j : Fin 8,
        cell limbs' j =
          cell limbs j +
            AspisR1BatchedFoldSourceStep.fold ((cs.map (fun c => c.product j)).sum) := by
  have hcount : (ActualOps ops).wideLimbCount = .ok 8#usize := rfl
  have holdBody :=
    AspisR1FastDotsNewOuterLimbLoopSegmentV1.fixed_batch_body_success_old_body
      (ActualOps ops) a a1 slot iter it' limbs limbs' hcount hbody
  exact AspisR1FastDotsActualBatchExactRootV1.current_batch_body_success_exact
    ops a a1 slot iter it' limbs limbs' houterEnd hcoords hstep holdBody

#print axioms v10_fixed_body_success_actual_batch_exact

end AspisR1FastDotsV10FixedBodyBatchExact
