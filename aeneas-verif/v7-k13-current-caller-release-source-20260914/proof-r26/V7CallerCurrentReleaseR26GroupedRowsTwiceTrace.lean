import V7CallerCurrentReleaseR26TailSixDispatch
import V7CallerCurrentReleaseR26GroupedRows

/-!
# Exact trace of the optimized grouped-rows-twice helper

The fused tail uses a specialized 16-way aggregation instead of invoking the
four-way grouped fold twice.  This module exposes its complete arithmetic
setup, generated basis, finite four-chunk trace, and exact returned row vector.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceTrace

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26GroupedRows

abbrev RawQM31 := field.QM31
abbrev OuterState :=
  core.slice.iter.ChunksExact Std.U8 × alloc.vec.Vec RawQM31

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

structure GroupedRowsTwiceSourceTrace
    (rowGroups : Slice Std.U8) (groupValues : Slice RawQM31)
    (alpha1 alpha2 : RawQM31)
    (foldedGroups : alloc.vec.Vec Std.U8)
    (foldedValues : alloc.vec.Vec RawQM31) : Type where
  alpha1Squared : RawQM31
  alpha2Squared : RawQM31
  alpha1Cubed : RawQM31
  alpha2Cubed : RawQM31
  basis : Array RawQM31 16#usize
  chunks : core.slice.iter.ChunksExact Std.U8
  alpha1SquareRun : field.QM31.square alpha1 = ok alpha1Squared
  alpha2SquareRun : field.QM31.square alpha2 = ok alpha2Squared
  alpha1CubeRun : field.QM31.mul alpha1Squared alpha1 = ok alpha1Cubed
  alpha2CubeRun : field.QM31.mul alpha2Squared alpha2 = ok alpha2Cubed
  basisRun : core.array.from_fn 16#usize
    sumcheck.fold_grouped_rows_twice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    (Array.make 4#usize
      [field.QM31.ONE, alpha1Cubed, alpha1Squared, alpha1],
     Array.make 4#usize
      [field.QM31.ONE, alpha2Cubed, alpha2Squared, alpha2]) = ok basis
  chunksRun : core.slice.Slice.chunks_exact rowGroups 16#usize = ok chunks
  loopTrace : ExactLoopTrace
    (fun state : OuterState =>
      sumcheck.fold_grouped_rows_twice_loop0.body groupValues basis state.1
        state.2)
    (chunks, alloc.vec.Vec.with_capacity RawQM31 4#usize) foldedValues
  groupsExact : foldedGroups = releasedRowGroups4

theorem grouped_rows_twice_exposes_trace
    (rowGroups : Slice Std.U8) (groupValues : Slice RawQM31)
    (alpha1 alpha2 : RawQM31)
    (foldedGroups : alloc.vec.Vec Std.U8)
    (foldedValues : alloc.vec.Vec RawQM31)
    (run : sumcheck.fold_grouped_rows_twice rowGroups groupValues alpha1
      alpha2 = ok (foldedGroups, foldedValues)) :
    Nonempty (GroupedRowsTwiceSourceTrace rowGroups groupValues alpha1 alpha2
      foldedGroups foldedValues) := by
  unfold sumcheck.fold_grouped_rows_twice at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨alpha1Squared, alpha1SquareRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨alpha2Squared, alpha2SquareRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨alpha1Cubed, alpha1CubeRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨alpha2Cubed, alpha2CubeRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨basis, basisRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨chunks, chunksRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨foldedValuesExpected, loopRun, run⟩ := run
  simp [Std.lift] at run
  obtain ⟨groupsRun, valuesExact⟩ := run
  have groupsExact : foldedGroups = releasedRowGroups4 := by
    calc
      foldedGroups =
          alloc.slice.Slice.into_vec
            (Array.make 4#usize [0#u8, 1#u8, 2#u8, 3#u8]
              sumcheck.fold_grouped_rows_twice._proof_1).to_slice := groupsRun.symm
      _ = releasedRowGroups4 := by
        apply Subtype.ext
        rfl
  subst foldedValuesExpected
  let loopTrace := Classical.choice (loop_success_yields_exact_trace
    (fun state : OuterState =>
      sumcheck.fold_grouped_rows_twice_loop0.body groupValues basis state.1
        state.2)
    (chunks, alloc.vec.Vec.with_capacity RawQM31 4#usize) foldedValues
    loopRun)
  exact ⟨{
    alpha1Squared := alpha1Squared
    alpha2Squared := alpha2Squared
    alpha1Cubed := alpha1Cubed
    alpha2Cubed := alpha2Cubed
    basis := basis
    chunks := chunks
    alpha1SquareRun := alpha1SquareRun
    alpha2SquareRun := alpha2SquareRun
    alpha1CubeRun := alpha1CubeRun
    alpha2CubeRun := alpha2CubeRun
    basisRun := basisRun
    chunksRun := chunksRun
    loopTrace := loopTrace
    groupsExact := groupsExact }⟩

#print axioms grouped_rows_twice_exposes_trace

end V7CallerCurrentReleaseR26GroupedRowsTwiceTrace
