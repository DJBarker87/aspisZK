import V7CallerCurrentReleaseR26GroupedRowsTwiceChunkTrace

/-!
# Exact four-chunk execution of the released fused grouped fold

The successful generated outer loop is forced through the four fixed chunks
in release order.  Each edge retains the complete per-chunk source trace.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceFourTrace

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedRowsTwiceTrace
open V7CallerCurrentReleaseR26GroupedRowsTwiceChunks
open V7CallerCurrentReleaseR26GroupedRowsTwiceChunkTrace

abbrev RawQM31 := field.QM31
abbrev OuterState :=
  core.slice.iter.ChunksExact Std.U8 × alloc.vec.Vec RawQM31

private def emptyRemainder : Slice Std.U8 := ⟨[], by scalar_tac⟩

def iter0 : core.slice.iter.ChunksExact Std.U8 := explicitIterator
def iter1 : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [chunk1, chunk2, chunk3], remainder := emptyRemainder }
def iter2 : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [chunk2, chunk3], remainder := emptyRemainder }
def iter3 : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [chunk3], remainder := emptyRemainder }
def iter4 : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [], remainder := emptyRemainder }

private theorem next0 :
    core.slice.iter.IteratorChunksExact.next iter0 =
      ok (some chunk0, iter1) := by rfl
private theorem next1 :
    core.slice.iter.IteratorChunksExact.next iter1 =
      ok (some chunk1, iter2) := by rfl
private theorem next2 :
    core.slice.iter.IteratorChunksExact.next iter2 =
      ok (some chunk2, iter3) := by rfl
private theorem next3 :
    core.slice.iter.IteratorChunksExact.next iter3 =
      ok (some chunk3, iter4) := by rfl
private theorem next4 :
    core.slice.iter.IteratorChunksExact.next iter4 =
      ok (none, iter4) := by rfl

def emptyValues : alloc.vec.Vec RawQM31 :=
  alloc.vec.Vec.with_capacity RawQM31 4#usize

structure ReleasedFourChunkTrace
    (groupValues : Slice RawQM31) (basis : Array RawQM31 16#usize)
    (foldedValues : alloc.vec.Vec RawQM31) : Type where
  values1 : alloc.vec.Vec RawQM31
  values2 : alloc.vec.Vec RawQM31
  values3 : alloc.vec.Vec RawQM31
  values4 : alloc.vec.Vec RawQM31
  step0 : OptimizedChunkTrace groupValues basis
    (iter0, emptyValues) (iter1, values1)
  step1 : OptimizedChunkTrace groupValues basis
    (iter1, values1) (iter2, values2)
  step2 : OptimizedChunkTrace groupValues basis
    (iter2, values2) (iter3, values3)
  step3 : OptimizedChunkTrace groupValues basis
    (iter3, values3) (iter4, values4)
  outputExact : foldedValues = values4

private theorem active_not_done
    (groupValues : Slice RawQM31) (basis : Array RawQM31 16#usize)
    (state : OuterState) (chunk : Slice Std.U8)
    (nextIterator : core.slice.iter.ChunksExact Std.U8)
    (output : alloc.vec.Vec RawQM31)
    (nextRun : core.slice.iter.IteratorChunksExact.next state.1 =
      ok (some chunk, nextIterator))
    (run : sumcheck.fold_grouped_rows_twice_loop0.body groupValues basis
      state.1 state.2 = ok (done output)) : False := by
  obtain ⟨nextState, impossible⟩ := active_body_result_is_continuation
    groupValues basis state chunk nextIterator (done output) nextRun run
  cases impossible

theorem released_outer_trace_exposes_four_chunks
    (groupValues : Slice RawQM31) (alpha1 alpha2 : RawQM31)
    (foldedGroups : alloc.vec.Vec Std.U8)
    (foldedValues : alloc.vec.Vec RawQM31)
    (source : GroupedRowsTwiceSourceTrace
      (alloc.vec.Vec.deref releasedRowGroups64) groupValues alpha1 alpha2
      foldedGroups foldedValues) :
    Nonempty (ReleasedFourChunkTrace groupValues source.basis foldedValues) := by
  have chunksExact : source.chunks = iter0 := by
    exact Result.ok.inj (source.chunksRun.symm.trans
      (by simpa [iter0] using released_chunks_exact_explicit))
  have execution : ExactLoopTrace
      (fun state : OuterState =>
        sumcheck.fold_grouped_rows_twice_loop0.body groupValues source.basis
          state.1 state.2)
      (iter0, emptyValues) foldedValues := by
    simpa [chunksExact, emptyValues] using source.loopTrace
  cases execution with
  | done equation =>
      exact False.elim (active_not_done groupValues source.basis
        (iter0, emptyValues) chunk0 iter1 foldedValues next0 equation)
  | @cont state0 state1 output0 equation0 tail0 =>
      obtain ⟨step0⟩ := continuation_exposes_chunk_trace
        groupValues source.basis (iter0, emptyValues) state1 equation0
      have nextPair0 : (some chunk0, iter1) =
          (some step0.chunk, step0.nextIterator) :=
        Result.ok.inj (next0.symm.trans step0.nextRun)
      have chunkExact0 : step0.chunk = chunk0 := by
        simpa using (congrArg Prod.fst nextPair0).symm
      have iteratorExact0 : step0.nextIterator = iter1 := by
        simpa using (congrArg Prod.snd nextPair0).symm
      have stateExact0 : state1 = (iter1, step0.nextValues) := by
        calc
          state1 = (step0.nextIterator, step0.nextValues) :=
            step0.successorExact
          _ = (iter1, step0.nextValues) := by rw [iteratorExact0]
      have step0' : OptimizedChunkTrace groupValues source.basis
          (iter0, emptyValues) (iter1, step0.nextValues) := by
        exact stateExact0 ▸ step0
      have tail0' : ExactLoopTrace
          (fun state : OuterState =>
            sumcheck.fold_grouped_rows_twice_loop0.body groupValues
              source.basis state.1 state.2)
          (iter1, step0.nextValues) foldedValues := by
        exact stateExact0 ▸ tail0
      cases tail0' with
      | done equation =>
          exact False.elim (active_not_done groupValues source.basis
            (iter1, step0.nextValues) chunk1 iter2 foldedValues next1 equation)
      | @cont state1' state2 output1 equation1 tail1 =>
          obtain ⟨step1⟩ := continuation_exposes_chunk_trace
            groupValues source.basis (iter1, step0.nextValues) state2 equation1
          have nextPair1 : (some chunk1, iter2) =
              (some step1.chunk, step1.nextIterator) :=
            Result.ok.inj (next1.symm.trans step1.nextRun)
          have chunkExact1 : step1.chunk = chunk1 := by
            simpa using (congrArg Prod.fst nextPair1).symm
          have iteratorExact1 : step1.nextIterator = iter2 := by
            simpa using (congrArg Prod.snd nextPair1).symm
          have stateExact1 : state2 = (iter2, step1.nextValues) := by
            calc
              state2 = (step1.nextIterator, step1.nextValues) :=
                step1.successorExact
              _ = (iter2, step1.nextValues) := by rw [iteratorExact1]
          have step1' : OptimizedChunkTrace groupValues source.basis
              (iter1, step0.nextValues) (iter2, step1.nextValues) := by
            exact stateExact1 ▸ step1
          have tail1' : ExactLoopTrace
              (fun state : OuterState =>
                sumcheck.fold_grouped_rows_twice_loop0.body groupValues
                  source.basis state.1 state.2)
              (iter2, step1.nextValues) foldedValues := by
            exact stateExact1 ▸ tail1
          cases tail1' with
          | done equation =>
              exact False.elim (active_not_done groupValues source.basis
                (iter2, step1.nextValues) chunk2 iter3 foldedValues next2
                equation)
          | @cont state2' state3 output2 equation2 tail2 =>
              obtain ⟨step2⟩ := continuation_exposes_chunk_trace
                groupValues source.basis (iter2, step1.nextValues) state3
                equation2
              have nextPair2 : (some chunk2, iter3) =
                  (some step2.chunk, step2.nextIterator) :=
                Result.ok.inj (next2.symm.trans step2.nextRun)
              have chunkExact2 : step2.chunk = chunk2 := by
                simpa using (congrArg Prod.fst nextPair2).symm
              have iteratorExact2 : step2.nextIterator = iter3 := by
                simpa using (congrArg Prod.snd nextPair2).symm
              have stateExact2 : state3 = (iter3, step2.nextValues) := by
                calc
                  state3 = (step2.nextIterator, step2.nextValues) :=
                    step2.successorExact
                  _ = (iter3, step2.nextValues) := by rw [iteratorExact2]
              have step2' : OptimizedChunkTrace groupValues source.basis
                  (iter2, step1.nextValues) (iter3, step2.nextValues) := by
                exact stateExact2 ▸ step2
              have tail2' : ExactLoopTrace
                  (fun state : OuterState =>
                    sumcheck.fold_grouped_rows_twice_loop0.body groupValues
                      source.basis state.1 state.2)
                  (iter3, step2.nextValues) foldedValues := by
                exact stateExact2 ▸ tail2
              cases tail2' with
              | done equation =>
                  exact False.elim (active_not_done groupValues source.basis
                    (iter3, step2.nextValues) chunk3 iter4 foldedValues next3
                    equation)
              | @cont state3' state4 output3 equation3 tail3 =>
                  obtain ⟨step3⟩ := continuation_exposes_chunk_trace
                    groupValues source.basis (iter3, step2.nextValues) state4
                    equation3
                  have nextPair3 : (some chunk3, iter4) =
                      (some step3.chunk, step3.nextIterator) :=
                    Result.ok.inj (next3.symm.trans step3.nextRun)
                  have chunkExact3 : step3.chunk = chunk3 := by
                    simpa using (congrArg Prod.fst nextPair3).symm
                  have iteratorExact3 : step3.nextIterator = iter4 := by
                    simpa using (congrArg Prod.snd nextPair3).symm
                  have stateExact3 : state4 =
                      (iter4, step3.nextValues) := by
                    calc
                      state4 = (step3.nextIterator, step3.nextValues) :=
                        step3.successorExact
                      _ = (iter4, step3.nextValues) := by rw [iteratorExact3]
                  have step3' : OptimizedChunkTrace groupValues source.basis
                      (iter3, step2.nextValues)
                      (iter4, step3.nextValues) := by
                    exact stateExact3 ▸ step3
                  have tail3' : ExactLoopTrace
                      (fun state : OuterState =>
                        sumcheck.fold_grouped_rows_twice_loop0.body groupValues
                          source.basis state.1 state.2)
                      (iter4, step3.nextValues) foldedValues := by
                    exact stateExact3 ▸ tail3
                  cases tail3' with
                  | done equation4 =>
                      have terminal := exhausted_body_result_is_done
                        groupValues source.basis
                        (iter4, step3.nextValues) iter4
                        (done foldedValues) next4 equation4
                      have outputExact : foldedValues = step3.nextValues := by
                        simpa using terminal
                      exact ⟨{
                        values1 := step0.nextValues
                        values2 := step1.nextValues
                        values3 := step2.nextValues
                        values4 := step3.nextValues
                        step0 := step0'
                        step1 := step1'
                        step2 := step2'
                        step3 := step3'
                        outputExact := outputExact }⟩
                  | @cont state4' state5 output4 equation4 tail4 =>
                      have terminal := exhausted_body_result_is_done
                        groupValues source.basis
                        (iter4, step3.nextValues) iter4
                        (cont state5) next4 equation4
                      cases terminal

#print axioms released_outer_trace_exposes_four_chunks

end V7CallerCurrentReleaseR26GroupedRowsTwiceFourTrace
