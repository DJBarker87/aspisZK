import V7CallerCurrentReleaseR26TerminalLineModel

/-!
# Complete generated terminal line source path

This file composes the zero-initialized sixteen-line accumulator, coefficient
reconstruction, the production four-product routine, deferred halving, and
the K1 model transport.  It is the symbolic unit consumed by the enclosing
`WeightAccumulator.dot` proof.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineSource

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26Qm31SumProducts4Semantics
open V7CallerCurrentReleaseR26TerminalLineBatch
open V7CallerCurrentReleaseR26TerminalLineBatchZero
open V7CallerCurrentReleaseR26TerminalLineCoefficients
open V7CallerCurrentReleaseR26TerminalLineArithmetic
open V7CallerCurrentReleaseR26TerminalLineModel

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

theorem generated_terminal_line_source_corresponds
    (deferred : Std.U8) (scales : Slice RawQM31) (xs : Slice RawM31)
    (values : Array RawQM31 4#usize)
    (scalesLength : scales.val.length = 16)
    (xsLength : xs.val.length = 16)
    (scalesCanonical : TerminalCanonicalQM31Slice scales)
    (xsCanonical : TerminalCanonicalM31Slice xs)
    (valuesCanonical : GeneratedCanonicalQM31Array4 values) :
    ∃ batch q0 q1 q2 q3 sum out,
      sumcheck.WeightAccumulator.impl.accumulate_line_batch_dot
          deferred scales xs deferred 0#usize zeroLineConstant zeroLineRaw
            zeroLineSums = ok batch ∧
      batch.1.val = 16 ∧
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () batch.2.1 = ok q0 ∧
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () batch.2.2.2.val[0]! = ok q1 ∧
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () batch.2.2.2.val[1]! = ok q2 ∧
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () batch.2.2.2.val[2]! = ok q3 ∧
      field.qm31_sum_products4 (terminalRawCoefficients q0 q1 q2 q3)
          values = ok sum ∧
      sumcheck.WeightAccumulator.impl.halve_qm31 sum deferred = ok out ∧
      GeneratedCanonicalQM31 out ∧
      sourceQm31ToModel (generatedQm31ToExact out) =
        terminalLineModelDot scales xs deferred.val values := by
  obtain ⟨batch, batchRun, countExact, constantCanonical, constantExact,
      sumsCanonical, _rawZero, sumsExact⟩ :=
    generated_terminal_line_batch_zero_corresponds deferred scales xs
      scalesLength xsLength scalesCanonical xsCanonical
  obtain ⟨q0, q1, q2, q3, q0Run, q1Run, q2Run, q3Run,
      coefficientsCanonical, coefficientsExact⟩ :=
    generated_terminal_line_coefficients_correspond scales xs batch.2.1
      batch.2.2.2 constantCanonical constantExact sumsCanonical sumsExact
  obtain ⟨sum, out, sumRun, halveRun, outCanonical, exact⟩ :=
    generated_terminal_line_arithmetic_corresponds scales xs
      (terminalRawCoefficients q0 q1 q2 q3) values deferred
      coefficientsCanonical coefficientsExact valuesCanonical
  have modelExact := terminal_line_halving_to_model scales xs deferred values
    out scalesLength xsLength exact
  exact ⟨batch, q0, q1, q2, q3, sum, out, batchRun, countExact,
    q0Run, q1Run, q2Run, q3Run, sumRun, halveRun, outCanonical, modelExact⟩

#print axioms generated_terminal_line_source_corresponds

end V7CallerCurrentReleaseR26TerminalLineSource
