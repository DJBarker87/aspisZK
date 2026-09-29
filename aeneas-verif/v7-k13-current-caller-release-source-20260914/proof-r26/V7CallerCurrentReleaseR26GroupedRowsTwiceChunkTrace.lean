import V7CallerCurrentReleaseR26GroupedRowsTwiceChunks

/-!
# Per-chunk trace of the optimized grouped two-fold helper

This module inverts one successful outer-loop continuation into the exact
sixteen-slot aggregation, contribution fold, four divisions by two, and vector
append performed by the generated source.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceChunkTrace

abbrev RawQM31 := field.QM31
abbrev OuterState :=
  core.slice.iter.ChunksExact Std.U8 × alloc.vec.Vec RawQM31

structure OptimizedChunkTrace
    (groupValues : Slice RawQM31) (basis : Array RawQM31 16#usize)
    (state nextState : OuterState) : Type where
  chunk : Slice Std.U8
  nextIterator : core.slice.iter.ChunksExact Std.U8
  uniqueGroups : Array Std.U8 16#usize
  coefficients : Array RawQM31 16#usize
  counts : Array Std.U8 16#usize
  firstSlots : Array Std.U8 16#usize
  uniqueLength : Std.Usize
  value : RawQM31
  half1 : RawQM31
  half2 : RawQM31
  half3 : RawQM31
  half4 : RawQM31
  nextValues : alloc.vec.Vec RawQM31
  nextRun : core.slice.iter.IteratorChunksExact.next state.1 =
    ok (some chunk, nextIterator)
  aggregationRun : sumcheck.fold_grouped_rows_twice_loop0_loop0 basis chunk
      (Array.repeat 16#usize 0#u8)
      (Array.repeat 16#usize field.QM31.ZERO)
      (Array.repeat 16#usize 0#u8)
      (Array.repeat 16#usize 0#u8) 0#usize 0#usize =
    ok (uniqueGroups, coefficients, counts, firstSlots, uniqueLength)
  contributionRun : sumcheck.fold_grouped_rows_twice_loop0_loop1
      groupValues uniqueGroups coefficients counts firstSlots uniqueLength
      field.QM31.ZERO 0#usize = ok value
  half1Run : field.QM31.half value = ok half1
  half2Run : field.QM31.half half1 = ok half2
  half3Run : field.QM31.half half2 = ok half3
  half4Run : field.QM31.half half3 = ok half4
  pushRun : alloc.vec.Vec.push state.2 half4 = ok nextValues
  successorExact : nextState = (nextIterator, nextValues)

theorem active_body_result_is_continuation
    (groupValues : Slice RawQM31) (basis : Array RawQM31 16#usize)
    (state : OuterState) (chunk : Slice Std.U8)
    (nextIterator : core.slice.iter.ChunksExact Std.U8)
    (flow : ControlFlow OuterState (alloc.vec.Vec RawQM31))
    (nextRun : core.slice.iter.IteratorChunksExact.next state.1 =
      ok (some chunk, nextIterator))
    (run : sumcheck.fold_grouped_rows_twice_loop0.body groupValues basis
      state.1 state.2 = ok flow) :
    ∃ nextState, flow = cont nextState := by
  unfold sumcheck.fold_grouped_rows_twice_loop0.body at run
  simp only [nextRun, bind_tc_ok] at run
  cases aggregationRun :
      sumcheck.fold_grouped_rows_twice_loop0_loop0 basis chunk
        (Array.repeat 16#usize 0#u8)
        (Array.repeat 16#usize field.QM31.ZERO)
        (Array.repeat 16#usize 0#u8)
        (Array.repeat 16#usize 0#u8) 0#usize 0#usize with
  | fail error => simp [aggregationRun] at run
  | div => simp [aggregationRun] at run
  | ok aggregate =>
      rcases aggregate with
        ⟨uniqueGroups, coefficients, counts, firstSlots, uniqueLength⟩
      simp only [aggregationRun, bind_tc_ok] at run
      cases contributionRun :
          sumcheck.fold_grouped_rows_twice_loop0_loop1 groupValues
            uniqueGroups coefficients counts firstSlots uniqueLength
            field.QM31.ZERO 0#usize with
      | fail error => simp [contributionRun] at run
      | div => simp [contributionRun] at run
      | ok value =>
          simp only [contributionRun, bind_tc_ok] at run
          cases half1Run : field.QM31.half value with
          | fail error => simp [half1Run] at run
          | div => simp [half1Run] at run
          | ok half1 =>
              simp only [half1Run, bind_tc_ok] at run
              cases half2Run : field.QM31.half half1 with
              | fail error => simp [half2Run] at run
              | div => simp [half2Run] at run
              | ok half2 =>
                  simp only [half2Run, bind_tc_ok] at run
                  cases half3Run : field.QM31.half half2 with
                  | fail error => simp [half3Run] at run
                  | div => simp [half3Run] at run
                  | ok half3 =>
                      simp only [half3Run, bind_tc_ok] at run
                      cases half4Run : field.QM31.half half3 with
                      | fail error => simp [half4Run] at run
                      | div => simp [half4Run] at run
                      | ok half4 =>
                          simp only [half4Run, bind_tc_ok] at run
                          cases pushRun : alloc.vec.Vec.push state.2 half4 with
                          | fail error => simp [pushRun] at run
                          | div => simp [pushRun] at run
                          | ok nextValues =>
                              simp only [pushRun, bind_tc_ok] at run
                              exact ⟨(nextIterator, nextValues),
                                Result.ok.inj run.symm⟩

theorem exhausted_body_result_is_done
    (groupValues : Slice RawQM31) (basis : Array RawQM31 16#usize)
    (state : OuterState) (nextIterator : core.slice.iter.ChunksExact Std.U8)
    (flow : ControlFlow OuterState (alloc.vec.Vec RawQM31))
    (nextRun : core.slice.iter.IteratorChunksExact.next state.1 =
      ok (none, nextIterator))
    (run : sumcheck.fold_grouped_rows_twice_loop0.body groupValues basis
      state.1 state.2 = ok flow) : flow = done state.2 := by
  unfold sumcheck.fold_grouped_rows_twice_loop0.body at run
  simp only [nextRun, bind_tc_ok] at run
  exact Result.ok.inj run.symm

theorem continuation_exposes_chunk_trace
    (groupValues : Slice RawQM31) (basis : Array RawQM31 16#usize)
    (state nextState : OuterState)
    (run : sumcheck.fold_grouped_rows_twice_loop0.body groupValues basis
      state.1 state.2 = ok (cont nextState)) :
    Nonempty (OptimizedChunkTrace groupValues basis state nextState) := by
  unfold sumcheck.fold_grouped_rows_twice_loop0.body at run
  cases nextRun : core.slice.iter.IteratorChunksExact.next state.1 with
  | fail error => simp [nextRun] at run
  | div => simp [nextRun] at run
  | ok nextPair =>
      rcases nextPair with ⟨nextOption, nextIterator⟩
      cases nextOption with
      | none => simp [nextRun] at run
      | some chunk =>
          simp only [nextRun, bind_tc_ok] at run
          cases aggregationRun :
              sumcheck.fold_grouped_rows_twice_loop0_loop0 basis chunk
                (Array.repeat 16#usize 0#u8)
                (Array.repeat 16#usize field.QM31.ZERO)
                (Array.repeat 16#usize 0#u8)
                (Array.repeat 16#usize 0#u8) 0#usize 0#usize with
          | fail error => simp [aggregationRun] at run
          | div => simp [aggregationRun] at run
          | ok aggregate =>
              rcases aggregate with
                ⟨uniqueGroups, coefficients, counts, firstSlots,
                  uniqueLength⟩
              simp only [aggregationRun, bind_tc_ok] at run
              cases contributionRun :
                  sumcheck.fold_grouped_rows_twice_loop0_loop1 groupValues
                    uniqueGroups coefficients counts firstSlots uniqueLength
                    field.QM31.ZERO 0#usize with
              | fail error => simp [contributionRun] at run
              | div => simp [contributionRun] at run
              | ok value =>
                  simp only [contributionRun, bind_tc_ok] at run
                  cases half1Run : field.QM31.half value with
                  | fail error => simp [half1Run] at run
                  | div => simp [half1Run] at run
                  | ok half1 =>
                      simp only [half1Run, bind_tc_ok] at run
                      cases half2Run : field.QM31.half half1 with
                      | fail error => simp [half2Run] at run
                      | div => simp [half2Run] at run
                      | ok half2 =>
                          simp only [half2Run, bind_tc_ok] at run
                          cases half3Run : field.QM31.half half2 with
                          | fail error => simp [half3Run] at run
                          | div => simp [half3Run] at run
                          | ok half3 =>
                              simp only [half3Run, bind_tc_ok] at run
                              cases half4Run : field.QM31.half half3 with
                              | fail error => simp [half4Run] at run
                              | div => simp [half4Run] at run
                              | ok half4 =>
                                  simp only [half4Run, bind_tc_ok] at run
                                  cases pushRun :
                                      alloc.vec.Vec.push state.2 half4 with
                                  | fail error => simp [pushRun] at run
                                  | div => simp [pushRun] at run
                                  | ok nextValues =>
                                      simp only [pushRun, bind_tc_ok] at run
                                      have successorExact : nextState =
                                          (nextIterator, nextValues) := by
                                        simpa using run.symm
                                      exact ⟨{
                                        chunk := chunk
                                        nextIterator := nextIterator
                                        uniqueGroups := uniqueGroups
                                        coefficients := coefficients
                                        counts := counts
                                        firstSlots := firstSlots
                                        uniqueLength := uniqueLength
                                        value := value
                                        half1 := half1
                                        half2 := half2
                                        half3 := half3
                                        half4 := half4
                                        nextValues := nextValues
                                        nextRun := nextRun
                                        aggregationRun := aggregationRun
                                        contributionRun := contributionRun
                                        half1Run := half1Run
                                        half2Run := half2Run
                                        half3Run := half3Run
                                        half4Run := half4Run
                                        pushRun := pushRun
                                        successorExact := successorExact }⟩

#print axioms continuation_exposes_chunk_trace
#print axioms active_body_result_is_continuation
#print axioms exhausted_body_result_is_done

end V7CallerCurrentReleaseR26GroupedRowsTwiceChunkTrace
