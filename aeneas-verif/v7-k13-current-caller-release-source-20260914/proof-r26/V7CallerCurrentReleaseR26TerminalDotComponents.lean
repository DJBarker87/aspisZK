import V7CallerCurrentReleaseR26TerminalDotLineTraversal
import V7CallerCurrentReleaseR26TerminalStructuredComponents
import V7CallerCurrentReleaseR26TerminalGroupedComponent

/-!
# Six-component terminal dot traversal

Starting from the optimized line contribution, the generated terminal loop
adds the two multilinear, released grouped, and two tensor contributions in
the accepted six-component order.  The line component's ordinary terminal
contribution is zero because it has already been accumulated by the optimized
line path.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalDotComponents

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26TerminalDotLineTraversal
open V7CallerCurrentReleaseR26TerminalStructuredComponents
open V7CallerCurrentReleaseR26TerminalGroupedComponent
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedRowsStaged
open V7CallerCurrentReleaseR26GroupedRowsSemantics
open AspisV5FriRelationCandidateBridge

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev Component := sumcheck.WeightComponent
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

private theorem zeroCanonical : GeneratedCanonicalQM31 field.QM31.ZERO := by
  norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31, field.QM31.ZERO]

private theorem generatedZeroExact :
    generatedQm31ToExact field.QM31.ZERO = 0 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [generatedQm31ToExact, generatedCm31ToExact, field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;>
      simp [generatedQm31ToExact, generatedCm31ToExact, field.QM31.ZERO]

theorem dot_terminal_six_corresponds
    (components : alloc.vec.Vec Component)
    (mScale0 mScale1 tScale0 tScale1 : RawQM31)
    (mPoint0 mPoint1 tFactors0 tFactors1 : alloc.vec.Vec RawQM31)
    (groupMasks : alloc.vec.Vec Std.U16)
    (g0 g1 g2 g3 : RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (deferred : Std.U8) (values : Slice RawQM31)
    (lineOut : RawQM31)
    (componentsExact : components.val =
      [.Multilinear mScale0 mPoint0,
       .Multilinear mScale1 mPoint1,
       .Grouped64x16BinaryDeferred releasedRowGroups4 groupMasks none
         (releasedFourValues g0 g1 g2 g3),
       .Tensor tScale0 tFactors0,
       .Tensor tScale1 tFactors1,
       .LineM31Batch lineScales lineXs deferred])
    (mScale0Canonical : GeneratedCanonicalQM31 mScale0)
    (mScale1Canonical : GeneratedCanonicalQM31 mScale1)
    (mPoint0Canonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        mPoint0.val)
    (mPoint1Canonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        mPoint1.val)
    (mPoint0Length : mPoint0.val.length = 2)
    (mPoint1Length : mPoint1.val.length = 2)
    (groupsCanonical : CanonicalFour g0 g1 g2 g3)
    (tScale0Canonical : GeneratedCanonicalQM31 tScale0)
    (tScale1Canonical : GeneratedCanonicalQM31 tScale1)
    (tFactors0Canonical :
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
        tFactors0.val)
    (tFactors1Canonical :
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
        tFactors1.val)
    (tFactors0Length : tFactors0.val.length = 2)
    (tFactors1Length : tFactors1.val.length = 2)
    (valuesCanonical : CanonicalSlice values)
    (valuesLength : values.length = 4)
    (lineOutCanonical : GeneratedCanonicalQM31 lineOut)
    (lineOutExact : sourceQm31ToModel (generatedQm31ToExact lineOut) =
      V7CallerCurrentReleaseR26TerminalLineModel.terminalLineModelDot
        (alloc.vec.Vec.deref lineScales) (alloc.vec.Vec.deref lineXs)
        deferred.val
        (Array.make 4#usize
          [values.val[0]!, values.val[1]!, values.val[2]!, values.val[3]!])) :
    ∃ out,
      sumcheck.WeightAccumulator.impl.dot_loop4 components values 0#usize
          lineOut = ok out ∧
      GeneratedCanonicalQM31 out ∧
      sourceQm31ToModel (generatedQm31ToExact out) =
        V7CallerCurrentReleaseR26TerminalLineModel.terminalLineModelDot
            (alloc.vec.Vec.deref lineScales) (alloc.vec.Vec.deref lineXs)
            deferred.val
            (Array.make 4#usize
              [values.val[0]!, values.val[1]!, values.val[2]!,
                values.val[3]!]) +
          multilinearTerminal mScale0 mPoint0.val[0]! mPoint0.val[1]!
            values +
          multilinearTerminal mScale1 mPoint1.val[0]! mPoint1.val[1]!
            values +
          candidateClaim
            (representedGroupedWeights releasedRowGroups4
              (releasedFourValues g0 g1 g2 g3))
            (terminalValues values) +
          tensorTerminal tScale0 tFactors0.val[0]! tFactors0.val[1]!
            values +
          tensorTerminal tScale1 tFactors1.val[0]! tFactors1.val[1]!
            values := by
  obtain ⟨c0, c0Run, c0Canonical, c0Exact⟩ :=
    dot_terminal_multilinear_corresponds mScale0 mPoint0 values
      mScale0Canonical mPoint0Canonical mPoint0Length valuesCanonical
      valuesLength
  obtain ⟨c1, c1Run, c1Canonical, c1Exact⟩ :=
    dot_terminal_multilinear_corresponds mScale1 mPoint1 values
      mScale1Canonical mPoint1Canonical mPoint1Length valuesCanonical
      valuesLength
  obtain ⟨c2, c2Run, c2Canonical, c2Exact⟩ :=
    dot_terminal_released_grouped_corresponds values groupMasks g0 g1 g2 g3
      valuesCanonical valuesLength groupsCanonical
  have c2Exact' : sourceQm31ToModel (generatedQm31ToExact c2) =
      candidateClaim
        (representedGroupedWeights releasedRowGroups4
          (releasedFourValues g0 g1 g2 g3))
        (terminalValues values) := by
    change exactRaw c2 = _
    exact c2Exact
  obtain ⟨c3, c3Run, c3Canonical, c3Exact⟩ :=
    dot_terminal_tensor_corresponds tScale0 tFactors0 values
      tScale0Canonical tFactors0Canonical tFactors0Length valuesCanonical
      valuesLength
  obtain ⟨c4, c4Run, c4Canonical, c4Exact⟩ :=
    dot_terminal_tensor_corresponds tScale1 tFactors1 values
      tScale1Canonical tFactors1Canonical tFactors1Length valuesCanonical
      valuesLength
  obtain ⟨s0, s0Run, s0Canonical, s0Exact⟩ :=
    generated_qm31_add_corresponds lineOut c0 lineOutCanonical c0Canonical
  obtain ⟨s1, s1Run, s1Canonical, s1Exact⟩ :=
    generated_qm31_add_corresponds s0 c1 s0Canonical c1Canonical
  obtain ⟨s2, s2Run, s2Canonical, s2Exact⟩ :=
    generated_qm31_add_corresponds s1 c2 s1Canonical c2Canonical
  obtain ⟨s3, s3Run, s3Canonical, s3Exact⟩ :=
    generated_qm31_add_corresponds s2 c3 s2Canonical c3Canonical
  obtain ⟨s4, s4Run, s4Canonical, s4Exact⟩ :=
    generated_qm31_add_corresponds s3 c4 s3Canonical c4Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_add_corresponds s4 field.QM31.ZERO s4Canonical
      zeroCanonical
  have mappedZero :
      sourceQm31ToModel (generatedQm31ToExact field.QM31.ZERO) = 0 := by
    rw [generatedZeroExact, sourceQm31ToModel_zero]
  have read0 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 0#usize =
      ok (.Multilinear mScale0 mPoint0) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      0#usize (by norm_num)
  have read1 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 1#usize =
      ok (.Multilinear mScale1 mPoint1) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      1#usize (by norm_num)
  have read2 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 2#usize =
      ok (.Grouped64x16BinaryDeferred releasedRowGroups4 groupMasks none
        (releasedFourValues g0 g1 g2 g3)) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      2#usize (by norm_num)
  have read3 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 3#usize =
      ok (.Tensor tScale0 tFactors0) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      3#usize (by norm_num)
  have read4 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 4#usize =
      ok (.Tensor tScale1 tFactors1) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      4#usize (by norm_num)
  have read5 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Component) components 5#usize =
      ok (.LineM31Batch lineScales lineXs deferred) := by
    simpa using componentAtSix components _ _ _ _ _ _ componentsExact
      5#usize (by norm_num)
  have component5Run :
      sumcheck.WeightAccumulator.impl.dot_terminal_component
          (.LineM31Batch lineScales lineXs deferred) values =
        ok field.QM31.ZERO := by
    rfl
  have step (index next : Std.Usize) (total contribution totalOut : RawQM31)
      (active : index.val < 6)
      (read : alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice Component) components index =
          ok components.val[index.val]!)
      (componentRun :
        sumcheck.WeightAccumulator.impl.dot_terminal_component
            components.val[index.val]! values = ok contribution)
      (addRun : field.QM31.add total contribution = ok totalOut)
      (succ : Std.Usize.wrapping_add index 1#usize = next) :
      sumcheck.WeightAccumulator.impl.dot_loop4.body components values index
          total = ok (cont (next, totalOut)) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop4.body
    rw [if_pos (by simpa [componentsExact]), read]
    simp only [bind_tc_ok]
    rw [componentRun]
    simp only [bind_tc_ok]
    rw [addRun]
    simp only [bind_tc_ok, Std.lift]
    rw [succ]
  have step0 := step 0#usize 1#usize lineOut c0 s0 (by norm_num)
    (by simpa [componentsExact] using read0)
    (by simpa [componentsExact] using c0Run) s0Run usizeZeroSucc
  have step1 := step 1#usize 2#usize s0 c1 s1 (by norm_num)
    (by simpa [componentsExact] using read1)
    (by simpa [componentsExact] using c1Run) s1Run usizeOneSucc
  have step2 := step 2#usize 3#usize s1 c2 s2 (by norm_num)
    (by simpa [componentsExact] using read2)
    (by simpa [componentsExact] using c2Run) s2Run usizeTwoSucc
  have step3 := step 3#usize 4#usize s2 c3 s3 (by norm_num)
    (by simpa [componentsExact] using read3)
    (by simpa [componentsExact] using c3Run) s3Run usizeThreeSucc
  have step4 := step 4#usize 5#usize s3 c4 s4 (by norm_num)
    (by simpa [componentsExact] using read4)
    (by simpa [componentsExact] using c4Run) s4Run usizeFourSucc
  have step5 := step 5#usize 6#usize s4 field.QM31.ZERO out (by norm_num)
    (by simpa [componentsExact] using read5)
    (by simpa [componentsExact] using component5Run) outRun usizeFiveSucc
  have done : sumcheck.WeightAccumulator.impl.dot_loop4.body components
      values 6#usize out = ok (done out) := by
    unfold sumcheck.WeightAccumulator.impl.dot_loop4.body
    simp [componentsExact]
  refine ⟨out, ?_, outCanonical, ?_⟩
  · unfold sumcheck.WeightAccumulator.impl.dot_loop4
    rw [loop.eq_1]
    simp only
    rw [step0]
    simp only [bind_tc_ok]
    rw [loop.eq_1]
    simp only
    rw [step1]
    simp only [bind_tc_ok]
    rw [loop.eq_1]
    simp only
    rw [step2]
    simp only [bind_tc_ok]
    rw [loop.eq_1]
    simp only
    rw [step3]
    simp only [bind_tc_ok]
    rw [loop.eq_1]
    simp only
    rw [step4]
    simp only [bind_tc_ok]
    rw [loop.eq_1]
    simp only
    rw [step5]
    simp only [bind_tc_ok]
    rw [loop.eq_1]
    simp only
    rw [done]
  · rw [outExact, s4Exact, s3Exact, s2Exact, s1Exact, s0Exact]
    simp only [sourceQm31ToModel_add]
    rw [lineOutExact, c0Exact, c1Exact, c2Exact', c3Exact, c4Exact]
    rw [mappedZero]
    ring

#print axioms dot_terminal_six_corresponds

end V7CallerCurrentReleaseR26TerminalDotComponents
