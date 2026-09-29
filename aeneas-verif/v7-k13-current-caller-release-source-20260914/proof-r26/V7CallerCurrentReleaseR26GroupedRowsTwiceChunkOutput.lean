import V7CallerCurrentReleaseR26GroupedRowsTwiceContributions

/-!
# Joining one optimized chunk trace to an exact output

This theorem is independent of the released chunk pattern.  Given exact
aggregation and contribution results, it identifies every recorded source
intermediate and the value appended after four divisions by two.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceChunkOutput

open V7CallerCurrentReleaseR26GroupedRowsTwiceChunkTrace

abbrev RawQM31 := field.QM31
abbrev OuterState :=
  core.slice.iter.ChunksExact Std.U8 × alloc.vec.Vec RawQM31

structure ChunkOutputMatch
    (groupValues : Slice RawQM31) (basis : Array RawQM31 16#usize)
    (state nextState : OuterState)
    (step : OptimizedChunkTrace groupValues basis state nextState)
    (value half1 half2 half3 half4 : RawQM31) : Prop where
  valueExact : step.value = value
  half1Exact : step.half1 = half1
  half2Exact : step.half2 = half2
  half3Exact : step.half3 = half3
  half4Exact : step.half4 = half4
  nextValuesExact : step.nextValues.val = state.2.val ++ [half4]

private theorem vecPushShape
    (input output : alloc.vec.Vec RawQM31) (value : RawQM31)
    (capacity : input.val.length < Std.Usize.max)
    (run : alloc.vec.Vec.push input value = ok output) :
    output.val = input.val ++ [value] := by
  obtain ⟨expected, expectedRun, expectedValues⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.push_spec input value capacity)
  rw [run] at expectedRun
  injection expectedRun with same
  subst expected
  exact expectedValues

theorem optimized_chunk_output_exact
    (groupValues : Slice RawQM31) (basis : Array RawQM31 16#usize)
    (state nextState : OuterState)
    (step : OptimizedChunkTrace groupValues basis state nextState)
    (uniqueGroups : Array Std.U8 16#usize)
    (coefficients : Array RawQM31 16#usize)
    (counts firstSlots : Array Std.U8 16#usize)
    (uniqueLength : Std.Usize)
    (value half1 half2 half3 half4 : RawQM31)
    (capacity : state.2.val.length < Std.Usize.max)
    (aggregationExpected :
      sumcheck.fold_grouped_rows_twice_loop0_loop0 basis step.chunk
        (Array.repeat 16#usize 0#u8)
        (Array.repeat 16#usize field.QM31.ZERO)
        (Array.repeat 16#usize 0#u8)
        (Array.repeat 16#usize 0#u8) 0#usize 0#usize =
      ok (uniqueGroups, coefficients, counts, firstSlots, uniqueLength))
    (contributionExpected :
      sumcheck.fold_grouped_rows_twice_loop0_loop1 groupValues uniqueGroups
        coefficients counts firstSlots uniqueLength field.QM31.ZERO 0#usize =
      ok value)
    (half1Expected : field.QM31.half value = ok half1)
    (half2Expected : field.QM31.half half1 = ok half2)
    (half3Expected : field.QM31.half half2 = ok half3)
    (half4Expected : field.QM31.half half3 = ok half4) :
    ChunkOutputMatch groupValues basis state nextState step
      value half1 half2 half3 half4 := by
  have aggregateEq := Result.ok.inj
    (step.aggregationRun.symm.trans aggregationExpected)
  have uniqueGroupsEq : step.uniqueGroups = uniqueGroups :=
    congrArg (fun aggregate => aggregate.1) aggregateEq
  have coefficientsEq : step.coefficients = coefficients :=
    congrArg (fun aggregate => aggregate.2.1) aggregateEq
  have countsEq : step.counts = counts :=
    congrArg (fun aggregate => aggregate.2.2.1) aggregateEq
  have firstSlotsEq : step.firstSlots = firstSlots :=
    congrArg (fun aggregate => aggregate.2.2.2.1) aggregateEq
  have uniqueLengthEq : step.uniqueLength = uniqueLength :=
    congrArg (fun aggregate => aggregate.2.2.2.2) aggregateEq
  have contributionActual := step.contributionRun
  rw [uniqueGroupsEq, coefficientsEq, countsEq, firstSlotsEq,
    uniqueLengthEq] at contributionActual
  have valueExact : step.value = value := Result.ok.inj
    (contributionActual.symm.trans contributionExpected)
  have half1Actual := step.half1Run
  rw [valueExact] at half1Actual
  have half1Exact : step.half1 = half1 := Result.ok.inj
    (half1Actual.symm.trans half1Expected)
  have half2Actual := step.half2Run
  rw [half1Exact] at half2Actual
  have half2Exact : step.half2 = half2 := Result.ok.inj
    (half2Actual.symm.trans half2Expected)
  have half3Actual := step.half3Run
  rw [half2Exact] at half3Actual
  have half3Exact : step.half3 = half3 := Result.ok.inj
    (half3Actual.symm.trans half3Expected)
  have half4Actual := step.half4Run
  rw [half3Exact] at half4Actual
  have half4Exact : step.half4 = half4 := Result.ok.inj
    (half4Actual.symm.trans half4Expected)
  have nextValuesExact := vecPushShape state.2 step.nextValues step.half4
    capacity step.pushRun
  rw [half4Exact] at nextValuesExact
  exact ⟨valueExact, half1Exact, half2Exact, half3Exact, half4Exact,
    nextValuesExact⟩

#print axioms optimized_chunk_output_exact

end V7CallerCurrentReleaseR26GroupedRowsTwiceChunkOutput
