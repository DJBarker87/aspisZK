import V7CallerCurrentReleaseR26TerminalLineBatchZero

/-!
# Reconstruction of the four optimized line coefficients

The completed batch stores each QM31 coefficient as four canonical M31
limbs.  This file reconstructs the constant coefficient and the three
nonconstant line-basis coefficients and identifies every exact limb sum.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineCoefficients

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31SumProducts4Semantics
open V7CallerCurrentReleaseR26TerminalLineLimbLoop
open V7CallerCurrentReleaseR26TerminalLineFlushLimb
open V7CallerCurrentReleaseR26TerminalLineReconstruction
open V7CallerCurrentReleaseR26TerminalLineBatch

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def terminalConstantExact (scales : Slice RawQM31) : ExactQM31 :=
  ⟨⟨terminalConstantPrefix scales 16 0,
     terminalConstantPrefix scales 16 1⟩,
   ⟨terminalConstantPrefix scales 16 2,
     terminalConstantPrefix scales 16 3⟩⟩

def terminalLineExact (scales : Slice RawQM31) (xs : Slice RawM31)
    (slot : Nat) : ExactQM31 :=
  ⟨⟨terminalLinePrefix scales xs 16 slot 0,
     terminalLinePrefix scales xs 16 slot 1⟩,
   ⟨terminalLinePrefix scales xs 16 slot 2,
     terminalLinePrefix scales xs 16 slot 3⟩⟩

def terminalExactCoefficient (scales : Slice RawQM31)
    (xs : Slice RawM31) (index : Nat) : ExactQM31 :=
  if index = 0 then terminalConstantExact scales
  else terminalLineExact scales xs (index - 1)

private theorem constantLimbsExact
    (scales : Slice RawQM31) (limbs : Array RawM31 4#usize)
    (exact : ∀ limb, limb < 4 →
      generatedM31ToExact (constantCell limbs limb) =
        terminalConstantPrefix scales 16 limb) :
    exactQm31OfLimbs limbs = terminalConstantExact scales := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simpa [exactQm31OfLimbs, terminalConstantExact, constantCell]
        using exact 0 (by norm_num)
    · simpa [exactQm31OfLimbs, terminalConstantExact, constantCell]
        using exact 1 (by norm_num)
  · apply QuadraticAlgebra.ext
    · simpa [exactQm31OfLimbs, terminalConstantExact, constantCell]
        using exact 2 (by norm_num)
    · simpa [exactQm31OfLimbs, terminalConstantExact, constantCell]
        using exact 3 (by norm_num)

private theorem lineLimbsCanonical
    (sums : Array (Array RawM31 4#usize) 3#usize)
    (canonical : CanonicalLineSums sums)
    (slot : Nat) (slotBound : slot < 3) :
    CanonicalFourLimbs sums.val[slot]! := by
  intro limb limbBound
  change GeneratedCanonicalM31 (sumCell sums slot limb)
  exact canonical slot slotBound limb limbBound

private theorem lineLimbsExact
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (sums : Array (Array RawM31 4#usize) 3#usize)
    (slot : Nat) (slotBound : slot < 3)
    (exact : ∀ row, row < 3 → ∀ limb, limb < 4 →
      generatedM31ToExact (sumCell sums row limb) =
        terminalLinePrefix scales xs 16 row limb) :
    exactQm31OfLimbs sums.val[slot]! = terminalLineExact scales xs slot := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simpa [exactQm31OfLimbs, terminalLineExact, sumCell]
        using exact slot slotBound 0 (by norm_num)
    · simpa [exactQm31OfLimbs, terminalLineExact, sumCell]
        using exact slot slotBound 1 (by norm_num)
  · apply QuadraticAlgebra.ext
    · simpa [exactQm31OfLimbs, terminalLineExact, sumCell]
        using exact slot slotBound 2 (by norm_num)
    · simpa [exactQm31OfLimbs, terminalLineExact, sumCell]
        using exact slot slotBound 3 (by norm_num)

def terminalRawCoefficients
    (q0 q1 q2 q3 : RawQM31) : Array RawQM31 4#usize :=
  Array.make 4#usize [q0, q1, q2, q3]

theorem generated_terminal_line_coefficients_correspond
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (constant : Array RawM31 4#usize)
    (sums : Array (Array RawM31 4#usize) 3#usize)
    (constantCanonical : CanonicalFourLimbs constant)
    (constantExact : ∀ limb, limb < 4 →
      generatedM31ToExact (constantCell constant limb) =
        terminalConstantPrefix scales 16 limb)
    (sumsCanonical : CanonicalLineSums sums)
    (sumsExact : ∀ slot, slot < 3 → ∀ limb, limb < 4 →
      generatedM31ToExact (sumCell sums slot limb) =
        terminalLinePrefix scales xs 16 slot limb) :
    ∃ q0 q1 q2 q3,
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () constant = ok q0 ∧
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () sums.val[0]! = ok q1 ∧
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () sums.val[1]! = ok q2 ∧
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () sums.val[2]! = ok q3 ∧
      GeneratedCanonicalQM31Array4 (terminalRawCoefficients q0 q1 q2 q3) ∧
      (∀ index, index < 4 →
        generatedQm31ToExact
            (terminalRawCoefficients q0 q1 q2 q3).val[index]! =
          terminalExactCoefficient scales xs index) := by
  obtain ⟨q0, q0Run, q0Canonical, q0Exact⟩ :=
    generated_terminal_qm31_from_limbs_corresponds constant constantCanonical
  obtain ⟨q1, q1Run, q1Canonical, q1Exact⟩ :=
    generated_terminal_qm31_from_limbs_corresponds sums.val[0]!
      (lineLimbsCanonical sums sumsCanonical 0 (by norm_num))
  obtain ⟨q2, q2Run, q2Canonical, q2Exact⟩ :=
    generated_terminal_qm31_from_limbs_corresponds sums.val[1]!
      (lineLimbsCanonical sums sumsCanonical 1 (by norm_num))
  obtain ⟨q3, q3Run, q3Canonical, q3Exact⟩ :=
    generated_terminal_qm31_from_limbs_corresponds sums.val[2]!
      (lineLimbsCanonical sums sumsCanonical 2 (by norm_num))
  have q0Exact' : generatedQm31ToExact q0 = terminalConstantExact scales := by
    rw [q0Exact]
    exact constantLimbsExact scales constant constantExact
  have q1Exact' : generatedQm31ToExact q1 = terminalLineExact scales xs 0 := by
    rw [q1Exact]
    exact lineLimbsExact scales xs sums 0 (by norm_num) sumsExact
  have q2Exact' : generatedQm31ToExact q2 = terminalLineExact scales xs 1 := by
    rw [q2Exact]
    exact lineLimbsExact scales xs sums 1 (by norm_num) sumsExact
  have q3Exact' : generatedQm31ToExact q3 = terminalLineExact scales xs 2 := by
    rw [q3Exact]
    exact lineLimbsExact scales xs sums 2 (by norm_num) sumsExact
  refine ⟨q0, q1, q2, q3, q0Run, q1Run, q2Run, q3Run, ?_, ?_⟩
  · intro index indexBound
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · change GeneratedCanonicalQM31 q0
      exact q0Canonical
    · change GeneratedCanonicalQM31 q1
      exact q1Canonical
    · change GeneratedCanonicalQM31 q2
      exact q2Canonical
    · change GeneratedCanonicalQM31 q3
      exact q3Canonical
  · intro index indexBound
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · change generatedQm31ToExact q0 = terminalExactCoefficient scales xs 0
      simpa [terminalExactCoefficient] using q0Exact'
    · change generatedQm31ToExact q1 = terminalExactCoefficient scales xs 1
      simpa [terminalExactCoefficient] using q1Exact'
    · change generatedQm31ToExact q2 = terminalExactCoefficient scales xs 2
      simpa [terminalExactCoefficient] using q2Exact'
    · change generatedQm31ToExact q3 = terminalExactCoefficient scales xs 3
      simpa [terminalExactCoefficient] using q3Exact'

#print axioms generated_terminal_line_coefficients_correspond

end V7CallerCurrentReleaseR26TerminalLineCoefficients
