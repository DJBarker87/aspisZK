import S4FromFnP6OuterSameClosureLoop0V1
import S4FromFnP6Loop0ArrayOpIrrelevanceV1
import S4FromFnP6CallbackOutputTransportV1
import FourDotsActualSevenBatchLimbBoundV2
import StepByScheduleV3

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

private theorem callback_success_output_matches_known_loop
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (q : Aeneas.Std.Array Std.U8 608#usize)
    (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) {value : aspis_core.field.wide_exact.WideExact}
    {c' : fast_dots.four_dots.closure}
    (hcall : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) slot = .ok (value,c'))
    (limbs : Aeneas.Std.Array Std.U64 8#usize)
    (vals : Aeneas.Std.Array Std.U32 8#usize)
    (hloop : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops) AspisR1FastDotsStepSchedule.startBy q g slot
      (Array.repeat 8#usize 0#u64) = .ok limbs)
    (harray : (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs = .ok vals) :
    ∃ optValue bodyValue tailValue,
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops).wideFromLimbs vals = .ok optValue ∧
      core.option.Option.unwrap optValue = .ok bodyValue ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops).wideAdd bodyValue tailValue = .ok value := by
  obtain ⟨limbs',vals',optValue,bodyValue,tailValue,hloop',harray',hwide,hunwrap,hadd⟩ :=
    generatedCallback_success_output_transport ops q g slot hcall
  have hlimbs : limbs' = limbs := Result.ok.inj (hloop'.symm.trans hloop)
  have harray'' := harray'
  rw [hlimbs] at harray''
  have hvals : vals' = vals := Result.ok.inj (harray''.symm.trans harray)
  rw [hvals] at hwide
  exact ⟨optValue,bodyValue,tailValue,hwide,hunwrap,hadd⟩

/-- One successful composed P6 N=4 constructor links each returned callback
output to its exact loop0 limbs, N=8 array and final wide-add. The retained
seven-batch bound is stated on those same loop limbs. P6/Rust std correspondence
and the caller's coordinate premise remain explicit. -/
theorem generatedFourDotsN4_success_output_linked_seven_bounds
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
      (limbs0 limbs1 limbs2 limbs3 : Aeneas.Std.Array Std.U64 8#usize)
      (vals0 vals1 vals2 vals3 : Aeneas.Std.Array Std.U32 8#usize)
      (opt0 opt1 opt2 opt3 : Option aspis_core.field.wide_exact.WideExact)
      (body0 body1 body2 body3 tail0 tail1 tail2 tail3 : aspis_core.field.wide_exact.WideExact),
      values.val = [v0,v1,v2,v3] ∧
      (∀ i : Fin 8, AspisR1FastDotsActualSevenBatchLimbBoundV2.cell limbs0 i ≤ 7 * AspisR1FastDotsActualSevenBatchLimbBoundV2.Cap) ∧
      (∀ i : Fin 8, AspisR1FastDotsActualSevenBatchLimbBoundV2.cell limbs1 i ≤ 7 * AspisR1FastDotsActualSevenBatchLimbBoundV2.Cap) ∧
      (∀ i : Fin 8, AspisR1FastDotsActualSevenBatchLimbBoundV2.cell limbs2 i ≤ 7 * AspisR1FastDotsActualSevenBatchLimbBoundV2.Cap) ∧
      (∀ i : Fin 8, AspisR1FastDotsActualSevenBatchLimbBoundV2.cell limbs3 i ≤ 7 * AspisR1FastDotsActualSevenBatchLimbBoundV2.Cap) ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (fourDotsOpsWithP6ArrayFromFnN4N8
            (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) limbs0 = .ok vals0 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).wideFromLimbs vals0 = .ok opt0 ∧
      core.option.Option.unwrap opt0 = .ok body0 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).wideAdd body0 tail0 = .ok v0 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (fourDotsOpsWithP6ArrayFromFnN4N8
            (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) limbs1 = .ok vals1 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).wideFromLimbs vals1 = .ok opt1 ∧
      core.option.Option.unwrap opt1 = .ok body1 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).wideAdd body1 tail1 = .ok v1 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (fourDotsOpsWithP6ArrayFromFnN4N8
            (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) limbs2 = .ok vals2 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).wideFromLimbs vals2 = .ok opt2 ∧
      core.option.Option.unwrap opt2 = .ok body2 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).wideAdd body2 tail2 = .ok v2 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (fourDotsOpsWithP6ArrayFromFnN4N8
            (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) limbs3 = .ok vals3 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).wideFromLimbs vals3 = .ok opt3 ∧
      core.option.Option.unwrap opt3 = .ok body3 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).wideAdd body3 tail3 = .ok v3 := by
  let actualOps := AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops
  obtain ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,vals0,vals1,vals2,vals3,
      hvalues,hcall0,hcall1,hcall2,hcall3,hstep,
      hloop0,harray0,hloop1,harray1,hloop2,harray2,hloop3,harray3⟩ :=
    generatedFourDotsN4_success_same_closure_loop0_four_calls actualOps q g h
  have hstartEq := Result.ok.inj (hstep.symm.trans AspisR1FastDotsStepSchedule.initialized_step_by)
  have hloop0Start : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (fourDotsOpsWithP6ArrayFromFnN4N8 actualOps) AspisR1FastDotsStepSchedule.startBy q g 0#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs0 := by simpa only [hstartEq] using hloop0
  have hloop1Start : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (fourDotsOpsWithP6ArrayFromFnN4N8 actualOps) AspisR1FastDotsStepSchedule.startBy q g 1#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs1 := by simpa only [hstartEq] using hloop1
  have hloop2Start : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (fourDotsOpsWithP6ArrayFromFnN4N8 actualOps) AspisR1FastDotsStepSchedule.startBy q g 2#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs2 := by simpa only [hstartEq] using hloop2
  have hloop3Start : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (fourDotsOpsWithP6ArrayFromFnN4N8 actualOps) AspisR1FastDotsStepSchedule.startBy q g 3#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs3 := by simpa only [hstartEq] using hloop3
  have hloopActual0 := hloop0Start
  have hloopActual1 := hloop1Start
  have hloopActual2 := hloop2Start
  have hloopActual3 := hloop3Start
  rw [generatedLoop0_ignores_p6_array_adapter actualOps _ q g 0#usize _] at hloopActual0
  rw [generatedLoop0_ignores_p6_array_adapter actualOps _ q g 1#usize _] at hloopActual1
  rw [generatedLoop0_ignores_p6_array_adapter actualOps _ q g 2#usize _] at hloopActual2
  rw [generatedLoop0_ignores_p6_array_adapter actualOps _ q g 3#usize _] at hloopActual3
  have hb0 := AspisR1FastDotsActualSevenBatchLimbBoundV2.actual_outer_startBy_success_seven_bound
    ops q g 0#usize limbs0 hcoords hloopActual0
  have hb1 := AspisR1FastDotsActualSevenBatchLimbBoundV2.actual_outer_startBy_success_seven_bound
    ops q g 1#usize limbs1 hcoords hloopActual1
  have hb2 := AspisR1FastDotsActualSevenBatchLimbBoundV2.actual_outer_startBy_success_seven_bound
    ops q g 2#usize limbs2 hcoords hloopActual2
  have hb3 := AspisR1FastDotsActualSevenBatchLimbBoundV2.actual_outer_startBy_success_seven_bound
    ops q g 3#usize limbs3 hcoords hloopActual3
  obtain ⟨opt0,body0,tail0,hwide0,hunwrap0,hadd0⟩ :=
    callback_success_output_matches_known_loop actualOps q g 0#usize hcall0 limbs0 vals0 hloop0Start harray0
  obtain ⟨opt1,body1,tail1,hwide1,hunwrap1,hadd1⟩ :=
    callback_success_output_matches_known_loop actualOps q g 1#usize hcall1 limbs1 vals1 hloop1Start harray1
  obtain ⟨opt2,body2,tail2,hwide2,hunwrap2,hadd2⟩ :=
    callback_success_output_matches_known_loop actualOps q g 2#usize hcall2 limbs2 vals2 hloop2Start harray2
  obtain ⟨opt3,body3,tail3,hwide3,hunwrap3,hadd3⟩ :=
    callback_success_output_matches_known_loop actualOps q g 3#usize hcall3 limbs3 vals3 hloop3Start harray3
  exact ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,vals0,vals1,vals2,vals3,
    opt0,opt1,opt2,opt3,body0,body1,body2,body3,tail0,tail1,tail2,tail3,
    hvalues,hb0,hb1,hb2,hb3,
    harray0,hwide0,hunwrap0,hadd0,
    harray1,hwide1,hunwrap1,hadd1,
    harray2,hwide2,hunwrap2,hadd2,
    harray3,hwide3,hunwrap3,hadd3⟩

#print axioms generatedFourDotsN4_success_output_linked_seven_bounds
end AspisR1FromFnP6Generated
