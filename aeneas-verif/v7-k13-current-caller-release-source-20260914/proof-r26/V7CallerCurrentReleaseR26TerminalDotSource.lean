import V7CallerCurrentReleaseR26TerminalDotModelIdentity

/-!
# Production terminal dot as the maintained K1 candidate claim

This theorem composes the accepted six-component weight-fold semantics with
the actual generated `WeightAccumulator.impl.dot` implementation at log
length two.  Every source branch in the optimized terminal path is discharged.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalDotSource

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26AcceptedWeightFoldSemantics
open V7CallerCurrentReleaseR26AcceptedWeightVectorSemantics
open V7CallerCurrentReleaseR26TerminalLineBatch
open V7CallerCurrentReleaseR26TerminalLineBatchZero
open V7CallerCurrentReleaseR26TerminalLineCoefficients
open V7CallerCurrentReleaseR26TerminalLineSource
open V7CallerCurrentReleaseR26TerminalDotLineTraversal
open V7CallerCurrentReleaseR26TerminalDotComponents
open V7CallerCurrentReleaseR26TerminalDotModelIdentity
open V7CallerCurrentReleaseR26TerminalStructuredComponents
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedRowsStaged
open V7CallerCurrentReleaseR26GroupedRowsSemantics
open AspisV5FriRelationCandidateBridge

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev Component := sumcheck.WeightComponent
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (bound : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using bound))
  have listBound : index.val < values.val.length := by
    simpa [Array.length_eq] using bound
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using listBound
  simpa [exact, listExact] using run

private theorem terminalXAt_eq_foldXAt
    (xs : Slice RawM31) (position : Nat)
    (bound : position < xs.val.length) :
    V7CallerCurrentReleaseR26TerminalLineBatch.terminalXAt xs position =
      V7CallerCurrentReleaseR26LineBatchFoldLoop.lineM31At xs position := by
  unfold V7CallerCurrentReleaseR26TerminalLineBatch.terminalXAt
    V7CallerCurrentReleaseR26LineBatchFoldLoop.lineM31At
  have left : xs.val[position] =
      @getElem! (List RawM31) Nat RawM31 _ _
        V7CallerCurrentReleaseR26TerminalLineBatch.instInhabitedRawM31
        xs.val position := by
    symm
    exact @List.getElem!_of_getElem? RawM31 xs.val[position]
      V7CallerCurrentReleaseR26TerminalLineBatch.instInhabitedRawM31
      xs.val position (by simp [bound])
  have right : xs.val[position] =
      @getElem! (List RawM31) Nat RawM31 _ _
        V7CallerCurrentReleaseR26LineBatchFoldLoop.instInhabitedRawM31
        xs.val position := by
    symm
    exact @List.getElem!_of_getElem? RawM31 xs.val[position]
      V7CallerCurrentReleaseR26LineBatchFoldLoop.instInhabitedRawM31
      xs.val position (by simp [bound])
  exact left.symm.trans right

theorem accepted_terminal_dot_corresponds
    {input : sumcheck.WeightAccumulator}
    {alphas : Array RawQM31 3#usize}
    {output : sumcheck.WeightAccumulator}
    {mScale0 mScale1 mScale2 : RawQM31}
    {mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31}
    {deferredAlpha : RawQM31} {groupValues : alloc.vec.Vec RawQM31}
    {tScale0 tScale1 : RawQM31}
    {tFactors0 tFactors1 : alloc.vec.Vec RawQM31}
    {lineScales : alloc.vec.Vec RawQM31}
    {lineXs : alloc.vec.Vec RawM31}
    (semantics : AcceptedWeightFoldSemantics input alphas output mScale0
      mScale1 mScale2 mPoint0 mPoint1 mPoint2 deferredAlpha groupValues
      tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs)
    (values : Slice RawQM31)
    (valuesCanonical : CanonicalSlice values)
    (valuesLength : values.length = 4) :
    ∃ out,
      sumcheck.WeightAccumulator.impl.dot output values = ok out ∧
      GeneratedCanonicalQM31 out ∧
      sourceQm31ToModel (generatedQm31ToExact out) =
        candidateClaim (outputWeightVector semantics) (terminalValues values) := by
  let vector := accepted_weight_vector_corresponds semantics
  let finalLineScales : alloc.vec.Vec RawQM31 :=
    ((alloc.vec.Vec.deref_mut
      ((alloc.vec.Vec.deref_mut lineScales).2
        semantics.tail.line.source.scalesOne)).2
      semantics.tail.line.source.scalesTwo)
  let finalLineXs : alloc.vec.Vec RawM31 :=
    ((alloc.vec.Vec.deref_mut
      ((alloc.vec.Vec.deref_mut lineXs).2
        semantics.tail.line.source.xsOne)).2
      semantics.tail.line.source.xsTwo)
  have lineScalesRoundtrip : alloc.vec.Vec.deref finalLineScales =
      semantics.tail.line.source.scalesTwo := by
    apply Subtype.ext
    rfl
  have lineXsRoundtrip : alloc.vec.Vec.deref finalLineXs =
      semantics.tail.line.source.xsTwo := by
    apply Subtype.ext
    rfl
  have componentsExact : output.components.val =
      [.Multilinear semantics.tail.multilinear0.source.scaleTwo
          semantics.tail.multilinear0.source.pointTwo,
       .Multilinear semantics.tail.multilinear1.source.scaleTwo
          semantics.tail.multilinear1.source.pointTwo,
       .Grouped64x16BinaryDeferred releasedRowGroups4
          semantics.first.source.groupMasksOut none
          (releasedFourValues semantics.tail.grouped.out0
            semantics.tail.grouped.out1 semantics.tail.grouped.out2
            semantics.tail.grouped.out3),
       .Tensor semantics.tail.tensor0.source.scaleTwo
          semantics.tail.tensor0.source.factorsTwo,
       .Tensor semantics.tail.tensor1.source.scaleTwo
          semantics.tail.tensor1.source.factorsTwo,
       .LineM31Batch finalLineScales finalLineXs
          semantics.tail.line.source.deferredTwo] := by
    rw [vector.outputComponentsExact]
    simp only [List.cons.injEq]
    exact ⟨semantics.tail.multilinear0.source.outputExact,
      semantics.tail.multilinear1.source.outputExact,
      semantics.tail.grouped.outputExact,
      semantics.tail.tensor0.source.outputExact,
      semantics.tail.tensor1.source.outputExact,
      semantics.tail.line.source.outputExact, True.intro⟩
  have terminalArrayCanonical := terminal_value_array_canonical values
    valuesCanonical valuesLength
  obtain ⟨batch, q0, q1, q2, q3, lineSum, lineOut, batchRun, countExact,
      q0Run, q1Run, q2Run, q3Run, sumRun, halveRun, lineOutCanonical,
      lineOutExact⟩ :=
    generated_terminal_line_source_corresponds
      semantics.tail.line.source.deferredTwo
      semantics.tail.line.source.scalesTwo semantics.tail.line.source.xsTwo
      (terminalValueArray values)
      semantics.tail.line.finalScalesLength semantics.tail.line.finalXsLength
      (by
        intro index bound
        exact semantics.tail.line.finalScalesCanonical index bound)
      (by
        intro index bound
        rw [terminalXAt_eq_foldXAt _ _ bound]
        exact semantics.tail.line.finalXsCanonical index bound)
      terminalArrayCanonical
  have batchRunFinal :
      sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot
          semantics.tail.line.source.deferredTwo
          (alloc.vec.Vec.deref finalLineScales)
          (alloc.vec.Vec.deref finalLineXs)
          semantics.tail.line.source.deferredTwo 0#usize zeroLineConstant
          zeroLineRaw zeroLineSums = ok batch := by
    rw [lineScalesRoundtrip, lineXsRoundtrip]
    exact batchRun
  have maxRun := dot_max_deferred_six output.components
    semantics.tail.multilinear0.source.scaleTwo
    semantics.tail.multilinear1.source.scaleTwo
    semantics.tail.tensor0.source.scaleTwo
    semantics.tail.tensor1.source.scaleTwo
    semantics.tail.multilinear0.source.pointTwo
    semantics.tail.multilinear1.source.pointTwo
    semantics.tail.tensor0.source.factorsTwo
    semantics.tail.tensor1.source.factorsTwo releasedRowGroups4
    semantics.first.source.groupMasksOut
    (releasedFourValues semantics.tail.grouped.out0 semantics.tail.grouped.out1
      semantics.tail.grouped.out2 semantics.tail.grouped.out3)
    finalLineScales finalLineXs semantics.tail.line.source.deferredTwo
    componentsExact
  have lineLoopRun :
      sumcheck.WeightAccumulator.impl.dot_loop1 output.components
          semantics.tail.line.source.deferredTwo 0#usize 0#usize
          (Array.repeat 4#usize field.M31.ZERO)
          (Array.repeat 3#usize (Array.repeat 4#usize 0#u64))
          (Array.repeat 3#usize (Array.repeat 4#usize field.M31.ZERO)) =
        ok batch := by
    simpa [zeroLineConstant, zeroLineRaw, zeroLineRawRow, zeroLineSums,
      zeroLineSumRow] using
      dot_accumulate_line_six output.components
        semantics.tail.multilinear0.source.scaleTwo
        semantics.tail.multilinear1.source.scaleTwo
        semantics.tail.tensor0.source.scaleTwo
        semantics.tail.tensor1.source.scaleTwo
        semantics.tail.multilinear0.source.pointTwo
        semantics.tail.multilinear1.source.pointTwo
        semantics.tail.tensor0.source.factorsTwo
        semantics.tail.tensor1.source.factorsTwo releasedRowGroups4
        semantics.first.source.groupMasksOut
        (releasedFourValues semantics.tail.grouped.out0
          semantics.tail.grouped.out1 semantics.tail.grouped.out2
          semantics.tail.grouped.out3)
        finalLineScales finalLineXs semantics.tail.line.source.deferredTwo
        batch componentsExact batchRunFinal
  obtain ⟨remainder, remainderRun, remainderVal⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Std.Usize.rem_spec batch.1 (y := 4#usize) (by norm_num))
  have remainderZero : remainder = 0#usize := by
    apply UScalar.eq_of_val_eq
    rw [remainderVal, countExact]
    norm_num
  have remRun : batch.1 % 4#usize = ok 0#usize := by
    simpa [remainderZero] using remainderRun
  have countNonzero : batch.1 ≠ 0#usize := by
    intro countZero
    have countZeroVal := congrArg UScalar.val countZero
    rw [countExact] at countZeroVal
    norm_num at countZeroVal
  have sumsRead0 := arrayIndexRun batch.2.2.2 0#usize (by norm_num)
  have sumsRead1 := arrayIndexRun batch.2.2.2 1#usize (by norm_num)
  have sumsRead2 := arrayIndexRun batch.2.2.2 2#usize (by norm_num)
  have valueRead0 := terminal_value_read values 0#usize (by
    simpa [valuesLength])
  have valueRead1 := terminal_value_read values 1#usize (by
    simpa [valuesLength])
  have valueRead2 := terminal_value_read values 2#usize (by
    simpa [valuesLength])
  have valueRead3 := terminal_value_read values 3#usize (by
    simpa [valuesLength])
  have q1RunScalar :
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () batch.2.2.2.val[(0#usize).val]! = ok q1 := by
    simpa using q1Run
  have q2RunScalar :
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () batch.2.2.2.val[(1#usize).val]! = ok q2 := by
    simpa using q2Run
  have q3RunScalar :
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () batch.2.2.2.val[(2#usize).val]! = ok q3 := by
    simpa using q3Run
  have lineOutExactFinal :
      sourceQm31ToModel (generatedQm31ToExact lineOut) =
        V7CallerCurrentReleaseR26TerminalLineModel.terminalLineModelDot
          (alloc.vec.Vec.deref finalLineScales)
          (alloc.vec.Vec.deref finalLineXs)
          semantics.tail.line.source.deferredTwo.val
          (terminalValueArray values) := by
    rw [lineScalesRoundtrip, lineXsRoundtrip]
    exact lineOutExact
  obtain ⟨out, terminalRun, outCanonical, outExact⟩ :=
    dot_terminal_six_corresponds output.components
      semantics.tail.multilinear0.source.scaleTwo
      semantics.tail.multilinear1.source.scaleTwo
      semantics.tail.tensor0.source.scaleTwo
      semantics.tail.tensor1.source.scaleTwo
      semantics.tail.multilinear0.source.pointTwo
      semantics.tail.multilinear1.source.pointTwo
      semantics.tail.tensor0.source.factorsTwo
      semantics.tail.tensor1.source.factorsTwo
      semantics.first.source.groupMasksOut
      semantics.tail.grouped.out0 semantics.tail.grouped.out1
      semantics.tail.grouped.out2 semantics.tail.grouped.out3
      finalLineScales finalLineXs semantics.tail.line.source.deferredTwo values
      lineOut componentsExact
      semantics.tail.multilinear0.finalScaleCanonical
      semantics.tail.multilinear1.finalScaleCanonical
      semantics.tail.multilinear0.finalPointCanonical
      semantics.tail.multilinear1.finalPointCanonical
      semantics.tail.multilinear0.finalPointLength
      semantics.tail.multilinear1.finalPointLength
      semantics.tail.grouped.finalValuesCanonical
      semantics.tail.tensor0.finalScaleCanonical
      semantics.tail.tensor1.finalScaleCanonical
      semantics.tail.tensor0.finalFactorsCanonical
      semantics.tail.tensor1.finalFactorsCanonical
      semantics.tail.tensor0.finalFactorsLength
      semantics.tail.tensor1.finalFactorsLength valuesCanonical valuesLength
      lineOutCanonical lineOutExactFinal
  have mPoint0Exact := vec_two_exact
    semantics.tail.multilinear0.source.pointTwo
    semantics.tail.multilinear0.finalPointLength
  have mPoint1Exact := vec_two_exact
    semantics.tail.multilinear1.source.pointTwo
    semantics.tail.multilinear1.finalPointLength
  have tFactors0Exact := vec_two_exact
    semantics.tail.tensor0.source.factorsTwo
    semantics.tail.tensor0.finalFactorsLength
  have tFactors1Exact := vec_two_exact
    semantics.tail.tensor1.source.factorsTwo
    semantics.tail.tensor1.finalFactorsLength
  have outExact' :
      sourceQm31ToModel (generatedQm31ToExact out) =
        V7CallerCurrentReleaseR26TerminalLineModel.terminalLineModelDot
              (alloc.vec.Vec.deref finalLineScales)
              (alloc.vec.Vec.deref finalLineXs)
              semantics.tail.line.source.deferredTwo.val
              (terminalValueArray values) +
            multilinearTerminal semantics.tail.multilinear0.source.scaleTwo
              semantics.tail.multilinear0.source.pointTwo.val[0]!
              semantics.tail.multilinear0.source.pointTwo.val[1]! values +
          multilinearTerminal semantics.tail.multilinear1.source.scaleTwo
            semantics.tail.multilinear1.source.pointTwo.val[0]!
            semantics.tail.multilinear1.source.pointTwo.val[1]! values +
        candidateClaim
          (representedGroupedWeights releasedRowGroups4
            (releasedFourValues semantics.tail.grouped.out0
              semantics.tail.grouped.out1 semantics.tail.grouped.out2
              semantics.tail.grouped.out3))
          (terminalValues values) +
      tensorTerminal semantics.tail.tensor0.source.scaleTwo
        semantics.tail.tensor0.source.factorsTwo.val[0]!
        semantics.tail.tensor0.source.factorsTwo.val[1]! values +
    tensorTerminal semantics.tail.tensor1.source.scaleTwo
      semantics.tail.tensor1.source.factorsTwo.val[0]!
      semantics.tail.tensor1.source.factorsTwo.val[1]! values := by
    simpa [terminalValueArray] using outExact
  have modelExact : sourceQm31ToModel (generatedQm31ToExact out) =
      candidateClaim (outputWeightVector semantics) (terminalValues values) := by
    rw [outExact']
    rw [terminal_six_sum_eq_candidate
      semantics.tail.multilinear0.source.scaleTwo
      semantics.tail.multilinear1.source.scaleTwo
      semantics.tail.tensor0.source.scaleTwo
      semantics.tail.tensor1.source.scaleTwo
      semantics.tail.multilinear0.source.pointTwo
      semantics.tail.multilinear1.source.pointTwo
      semantics.tail.tensor0.source.factorsTwo
      semantics.tail.tensor1.source.factorsTwo
      semantics.tail.grouped.out0 semantics.tail.grouped.out1
      semantics.tail.grouped.out2 semantics.tail.grouped.out3
      (alloc.vec.Vec.deref finalLineScales)
      (alloc.vec.Vec.deref finalLineXs)
      semantics.tail.line.source.deferredTwo.val values
      mPoint0Exact mPoint1Exact tFactors0Exact tFactors1Exact]
    unfold outputWeightVector
    rw [lineScalesRoundtrip, lineXsRoundtrip]
    rw [semantics.tail.grouped.finalGroupsExact,
      semantics.tail.grouped.finalValuesExact]
    rfl
  have valuesLengthScalar : Slice.len values = 4#usize := by
    apply UScalar.eq_of_val_eq
    simpa using valuesLength
  refine ⟨out, ?_, outCanonical, modelExact⟩
  unfold sumcheck.WeightAccumulator.impl.dot
  rw [if_pos vector.outputLogExact, if_pos valuesLengthScalar, maxRun]
  simp only [bind_tc_ok]
  rw [lineLoopRun]
  simp only [bind_tc_ok]
  rw [remRun]
  simp only [bind_tc_ok]
  rw [if_neg (by simp), if_neg countNonzero]
  rw [q0Run]
  simp only [bind_tc_ok]
  rw [sumsRead0]
  simp only [bind_tc_ok]
  rw [q1RunScalar]
  simp only [bind_tc_ok]
  rw [sumsRead1]
  simp only [bind_tc_ok]
  rw [q2RunScalar]
  simp only [bind_tc_ok]
  rw [sumsRead2]
  simp only [bind_tc_ok]
  rw [q3RunScalar]
  simp only [bind_tc_ok]
  rw [valueRead0]
  simp only [bind_tc_ok]
  rw [valueRead1]
  simp only [bind_tc_ok]
  rw [valueRead2]
  simp only [bind_tc_ok]
  rw [valueRead3]
  simp only [bind_tc_ok]
  change (do
    let lineSum' ← field.qm31_sum_products4
      (terminalRawCoefficients q0 q1 q2 q3) (terminalValueArray values)
    let lineOut' ← sumcheck.WeightAccumulator.impl.halve_qm31 lineSum'
      semantics.tail.line.source.deferredTwo
    sumcheck.WeightAccumulator.impl.dot_loop4 output.components values
      0#usize lineOut') = ok out
  rw [sumRun]
  simp only [bind_tc_ok]
  rw [halveRun]
  simp only [bind_tc_ok]
  exact terminalRun

#print axioms accepted_terminal_dot_corresponds

end V7CallerCurrentReleaseR26TerminalDotSource
