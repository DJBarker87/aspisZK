import V7CallerCurrentReleaseR26TerminalLineHalving

/-!
# K1 terminal form of a folded line batch

This file isolates the mathematical target of the optimized source
accumulator.  At log length one, each line contributes the four natural-basis
coefficients `[1, x, 2x²-1, x(2x²-1)]`, followed by the deferred power-of-two
division.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std
open scoped BigOperators
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineClaim

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26TerminalStructuredComponents
open AspisCircleTensorBinding
open AspisV5FriRelationCandidateBridge
open AspisV5FriNaturalBasisRadix4

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ModelM31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def terminalLinePolynomial (x : ModelQM31) (values : Fin 4 → ModelQM31) :
    ModelQM31 :=
  values 0 + x * values 1 + doubledFactor x 1 * values 2 +
    x * doubledFactor x 1 * values 3

def terminalLineContribution (scale x : ModelQM31) (deferred : Nat)
    (values : Fin 4 → ModelQM31) : ModelQM31 :=
  values 0 * (scale * 1 / (2 : ModelQM31) ^ deferred) +
    values 1 * (scale * x / (2 : ModelQM31) ^ deferred) +
    values 2 * (scale * doubledFactor x 1 / (2 : ModelQM31) ^ deferred) +
    values 3 *
      (scale * (x * doubledFactor x 1) / (2 : ModelQM31) ^ deferred)

private theorem naturalLineValue_zero (x : ModelQM31) :
    naturalLineValue x 0 = 1 := by
  simp [naturalLineValue]

private theorem naturalLineValue_one (x : ModelQM31) :
    naturalLineValue x 1 = x := by
  simpa [naturalLineValue] using naturalLineValue_two_mul_add_one x 0

private theorem naturalLineValue_two (x : ModelQM31) :
    naturalLineValue x 2 = doubledFactor x 1 := by
  rw [show 2 = 2 * 1 by omega, naturalLineValue_two_mul]
  simpa [naturalLineValue] using
    naturalLineValue_two_mul_add_one (doubledFactor x 1) 0

private theorem naturalLineValue_three (x : ModelQM31) :
    naturalLineValue x 3 = x * doubledFactor x 1 := by
  rw [show 3 = 2 * 1 + 1 by omega, naturalLineValue_two_mul_add_one]
  rw [naturalLineValue_one]

def lineBatchWeightsOne (scales : Slice RawQM31) (xs : Slice RawM31)
    (deferred : Nat) : Fin 4 → ModelQM31 :=
  fun index => ∑ position : Fin 16,
    lineWeightAt (lineQM31At scales position.val)
      (lineM31At xs position.val) deferred index.val

theorem lineWeightAt_terminal_zero
    (scale : RawQM31) (x : RawM31) (deferred : Nat) :
    lineWeightAt scale x deferred 0 =
      exactRaw scale / (2 : ModelQM31) ^ deferred := by
  unfold lineWeightAt
  rw [naturalLineValue_zero]
  rw [mul_one]

theorem lineWeightAt_terminal_one
    (scale : RawQM31) (x : RawM31) (deferred : Nat) :
    lineWeightAt scale x deferred 1 =
      exactRaw scale *
        algebraMap ModelM31 ModelQM31 (generatedM31ToExact x) /
          (2 : ModelQM31) ^ deferred := by
  unfold lineWeightAt
  rw [naturalLineValue_one]

theorem lineWeightAt_terminal_two
    (scale : RawQM31) (x : RawM31) (deferred : Nat) :
    lineWeightAt scale x deferred 2 =
      exactRaw scale *
        doubledFactor
          (algebraMap ModelM31 ModelQM31 (generatedM31ToExact x)) 1 /
          (2 : ModelQM31) ^ deferred := by
  unfold lineWeightAt
  rw [naturalLineValue_two]

theorem lineWeightAt_terminal_three
    (scale : RawQM31) (x : RawM31) (deferred : Nat) :
    lineWeightAt scale x deferred 3 =
      exactRaw scale *
        (algebraMap ModelM31 ModelQM31 (generatedM31ToExact x) *
          doubledFactor
            (algebraMap ModelM31 ModelQM31 (generatedM31ToExact x)) 1) /
          (2 : ModelQM31) ^ deferred := by
  unfold lineWeightAt
  rw [naturalLineValue_three]

#print axioms lineWeightAt_terminal_zero
#print axioms lineWeightAt_terminal_one
#print axioms lineWeightAt_terminal_two
#print axioms lineWeightAt_terminal_three

end V7CallerCurrentReleaseR26TerminalLineClaim
