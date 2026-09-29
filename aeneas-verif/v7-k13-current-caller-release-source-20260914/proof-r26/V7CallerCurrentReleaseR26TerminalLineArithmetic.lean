import V7CallerCurrentReleaseR26TerminalLineCoefficients

/-!
# Final optimized line arithmetic

This file composes the production four-product QM31 routine with the deferred
halving loop.  The resulting equation is stated directly over the four exact
line coefficients, so the later `dot` proof does not unfold either arithmetic
implementation.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open scoped BigOperators
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineArithmetic

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31SumProducts4Semantics
open V7CallerCurrentReleaseR26TerminalLineHalving
open V7CallerCurrentReleaseR26TerminalLineCoefficients

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def terminalExactDot (scales : Slice RawQM31) (xs : Slice RawM31)
    (values : Array RawQM31 4#usize) : ExactQM31 :=
  ∑ index ∈ Finset.range 4,
    terminalExactCoefficient scales xs index *
      generatedQm31ToExact values.val[index]!

theorem generated_terminal_line_arithmetic_corresponds
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (coefficients values : Array RawQM31 4#usize)
    (deferred : Std.U8)
    (coefficientsCanonical : GeneratedCanonicalQM31Array4 coefficients)
    (coefficientsExact : ∀ index, index < 4 →
      generatedQm31ToExact coefficients.val[index]! =
        terminalExactCoefficient scales xs index)
    (valuesCanonical : GeneratedCanonicalQM31Array4 values) :
    ∃ sum out,
      field.qm31_sum_products4 coefficients values = ok sum ∧
      sumcheck.WeightAccumulator.impl.halve_qm31 sum deferred = ok out ∧
      GeneratedCanonicalQM31 out ∧
      (2 : ExactQM31) ^ deferred.val * generatedQm31ToExact out =
        terminalExactDot scales xs values := by
  obtain ⟨sum, sumRun, sumCanonical, sumExact⟩ :=
    generated_qm31_sum_products4_corresponds coefficients values
      coefficientsCanonical valuesCanonical
  have sumExact' : generatedQm31ToExact sum =
      terminalExactDot scales xs values := by
    rw [sumExact]
    unfold exactProductDot4 terminalExactDot
    apply Finset.sum_congr rfl
    intro index indexMem
    rw [coefficientsExact index (by simpa using indexMem)]
  obtain ⟨out, halveRun, outCanonical, outExact⟩ :=
    generated_halve_qm31_corresponds sum deferred sumCanonical
  refine ⟨sum, out, sumRun, halveRun, outCanonical, ?_⟩
  rw [outExact, sumExact']

#print axioms generated_terminal_line_arithmetic_corresponds

end V7CallerCurrentReleaseR26TerminalLineArithmetic
