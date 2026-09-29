import V7CallerCurrentReleaseR26TerminalLineArithmetic
import V7CallerCurrentReleaseR26K1QueryWeightBridge

/-!
# Line coefficient identity in the source exact field

The limb-oriented accumulator coefficients are identified with the natural
line basis already used by the K1 bridge.  This is the semantic join between
the optimized representation and the maintained line-weight model.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std
open scoped BigOperators
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineCoefficientIdentity

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26LineBatchFactorLoop
open V7CallerCurrentReleaseR26QueryWeightSemantics
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26TerminalLineAccumulator
open V7CallerCurrentReleaseR26TerminalLineBatch
open V7CallerCurrentReleaseR26TerminalLineCoefficients

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

private theorem exactNaturalLineValue_zero
    (x : V7CallerCurrentReleaseR26FieldBridge.ExactM31) :
    exactNaturalLineValue x 0 = 1 := by
  simp [exactNaturalLineValue]

private theorem exactNaturalLineValue_one
    (x : V7CallerCurrentReleaseR26FieldBridge.ExactM31) :
    exactNaturalLineValue x 1 = ⟨⟨x, 0⟩, 0⟩ := by
  simp [exactNaturalLineValue, lineFactor]

private theorem exactNaturalLineValue_two
    (x : V7CallerCurrentReleaseR26FieldBridge.ExactM31) :
    exactNaturalLineValue x 2 = ⟨⟨2 * x ^ 2 - 1, 0⟩, 0⟩ := by
  have bits : (Nat.bitIndices 2).toFinset = {1} := by decide
  rw [exactNaturalLineValue, bits]
  simp [lineFactor]

private theorem exactNaturalLineValue_three
    (x : V7CallerCurrentReleaseR26FieldBridge.ExactM31) :
    exactNaturalLineValue x 3 = ⟨⟨x * (2 * x ^ 2 - 1), 0⟩, 0⟩ := by
  have bits : (Nat.bitIndices 3).toFinset = {0, 1} := by decide
  rw [exactNaturalLineValue, bits]
  simp [lineFactor]

private theorem sum_re_re {T : Type} [DecidableEq T] (values : Finset T)
    (term : T → ExactQM31) :
    (∑ index ∈ values, term index).re.re =
      ∑ index ∈ values, (term index).re.re := by
  induction values using Finset.induction_on with
  | empty => simp
  | @insert value values fresh ih => simp [fresh, ih]

private theorem sum_re_im {T : Type} [DecidableEq T] (values : Finset T)
    (term : T → ExactQM31) :
    (∑ index ∈ values, term index).re.im =
      ∑ index ∈ values, (term index).re.im := by
  induction values using Finset.induction_on with
  | empty => simp
  | @insert value values fresh ih => simp [fresh, ih]

private theorem sum_im_re {T : Type} [DecidableEq T] (values : Finset T)
    (term : T → ExactQM31) :
    (∑ index ∈ values, term index).im.re =
      ∑ index ∈ values, (term index).im.re := by
  induction values using Finset.induction_on with
  | empty => simp
  | @insert value values fresh ih => simp [fresh, ih]

private theorem sum_im_im {T : Type} [DecidableEq T] (values : Finset T)
    (term : T → ExactQM31) :
    (∑ index ∈ values, term index).im.im =
      ∑ index ∈ values, (term index).im.im := by
  induction values using Finset.induction_on with
  | empty => simp
  | @insert value values fresh ih => simp [fresh, ih]

theorem terminal_exact_coefficient_natural_basis
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (index : Nat) (indexBound : index < 4) :
    terminalExactCoefficient scales xs index =
      ∑ position ∈ Finset.range 16,
        generatedQm31ToExact (terminalScaleAt scales position) *
          exactNaturalLineValue
            (generatedM31ToExact (terminalXAt xs position)) index := by
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · rw [sum_re_re]
        simp [terminalExactCoefficient, terminalConstantExact,
          terminalLineExact, terminalConstantPrefix, terminalLinePrefix,
          exactScaleLimb, scaleLimb, exactLineFactor,
          terminalScaleAt, terminalXAt, generatedQm31ToExact,
          generatedCm31ToExact, exactNaturalLineValue_zero,
          exactNaturalLineValue_one, exactNaturalLineValue_two,
          exactNaturalLineValue_three]
      · rw [sum_re_im]
        simp [terminalExactCoefficient, terminalConstantExact,
          terminalLineExact, terminalConstantPrefix, terminalLinePrefix,
          exactScaleLimb, scaleLimb, exactLineFactor,
          terminalScaleAt, terminalXAt, generatedQm31ToExact,
          generatedCm31ToExact, exactNaturalLineValue_zero,
          exactNaturalLineValue_one, exactNaturalLineValue_two,
          exactNaturalLineValue_three]
    · apply QuadraticAlgebra.ext
      · rw [sum_im_re]
        simp [terminalExactCoefficient, terminalConstantExact,
          terminalLineExact, terminalConstantPrefix, terminalLinePrefix,
          exactScaleLimb, scaleLimb, exactLineFactor,
          terminalScaleAt, terminalXAt, generatedQm31ToExact,
          generatedCm31ToExact, exactNaturalLineValue_zero,
          exactNaturalLineValue_one, exactNaturalLineValue_two,
          exactNaturalLineValue_three]
      · rw [sum_im_im]
        simp [terminalExactCoefficient, terminalConstantExact,
          terminalLineExact, terminalConstantPrefix, terminalLinePrefix,
          exactScaleLimb, scaleLimb, exactLineFactor,
          terminalScaleAt, terminalXAt, generatedQm31ToExact,
          generatedCm31ToExact, exactNaturalLineValue_zero,
          exactNaturalLineValue_one, exactNaturalLineValue_two,
          exactNaturalLineValue_three]

#print axioms terminal_exact_coefficient_natural_basis

end V7CallerCurrentReleaseR26TerminalLineCoefficientIdentity
