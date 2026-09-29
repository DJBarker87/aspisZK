import V7CallerCurrentReleaseR26LineBatchFold
import V7CallerCurrentReleaseR26K1StructuredWeightBridge
import AspisFormal.V5FriNaturalBasisRadix4

/-!
# Current line-batch folds in the maintained K1 model

The source multiplies each line scale by an arity-four numerator, advances
the line coordinate twice, and defers the two divisions by two.  This file
shows that representation change is exactly one K1 `dualWeightFoldLayer`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open scoped BigOperators

namespace V7CallerCurrentReleaseR26K1LineBatchFoldBridge

open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26LineBatchFoldStep
open V7CallerCurrentReleaseR26LineBatchFactorLoop
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26LineBatchFold
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open AspisCircleTensorBinding
open AspisV5FriNaturalBasisRadix4
open AspisV5FriRelationCandidateBridge
open AspisV5ComponentCConcreteFoldLinearity

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev SourceM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev SourceQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31
abbrev ModelM31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def lineWeightAt (scale : RawQM31) (x : RawM31)
    (deferred index : Nat) : ModelQM31 :=
  exactRaw scale *
      naturalLineValue
        (algebraMap ModelM31 ModelQM31 (generatedM31ToExact x)) index /
    (2 : ModelQM31) ^ deferred

def lineBatchComponentWeights (rounds : Nat)
    (scales : Slice RawQM31) (xs : Slice RawM31) (deferred : Nat) :
    Fin (radix4Size rounds) → ModelQM31 :=
  fun index => ∑ position : Fin 16,
    lineWeightAt scales.val[position.val]! xs.val[position.val]!
      deferred index.val

@[simp] private theorem sourceQm31ToModel_pow
    (value : SourceQM31) (power : Nat) :
    sourceQm31ToModel (value ^ power) =
      sourceQm31ToModel value ^ power := by
  change sourceQm31ToModelHom (value ^ power) =
    sourceQm31ToModelHom value ^ power
  exact map_pow sourceQm31ToModelHom value power

@[simp] private theorem sourceQm31ToModel_exactEmbedM31 (x : SourceM31) :
    sourceQm31ToModel (exactEmbedM31 x) =
      algebraMap ModelM31 ModelQM31 x := by
  rfl

private theorem mappedLineBatchFoldNumerator
    (alpha : SourceQM31) (x : SourceM31) :
    sourceQm31ToModel (lineBatchFoldNumerator alpha x) =
      1 + sourceQm31ToModel alpha ^ 3 *
          algebraMap ModelM31 ModelQM31 x +
        sourceQm31ToModel alpha ^ 2 *
          doubledFactor (algebraMap ModelM31 ModelQM31 x) 1 +
        sourceQm31ToModel alpha *
          (doubledFactor (algebraMap ModelM31 ModelQM31 x) 1 *
            algebraMap ModelM31 ModelQM31 x) := by
  simp [lineBatchFoldNumerator, doubledM31, doubledFactor]
  rw [map_ofNat]

private theorem doubledTwice_eq_doubledFactorTwo (x : SourceM31) :
    algebraMap ModelM31 ModelQM31 (doubledM31 (doubledM31 x)) =
      doubledFactor (algebraMap ModelM31 ModelQM31 x) 2 := by
  change modelEmbedM31 (doubledM31 (doubledM31 x)) = _
  have exactInput : doubledM31 (doubledM31 x) = lineFactor x 2 := by
    rfl
  rw [exactInput]
  exact embedded_lineFactor_eq_doubledFactor x 2

private theorem dualWeightFoldValue_lineWeightAt
    (scale xScale : RawQM31) (x xOut : RawM31)
    (alpha : RawQM31) (deferred : Nat) (fibre : Nat)
    (scaleExact : generatedQm31ToExact xScale =
      generatedQm31ToExact scale *
        lineBatchFoldNumerator (generatedQm31ToExact alpha)
          (generatedM31ToExact x))
    (xExact : generatedM31ToExact xOut =
      doubledM31 (doubledM31 (generatedM31ToExact x))) :
    dualWeightFoldValue (exactRaw alpha)
        (fun slot => lineWeightAt scale x deferred (4 * fibre + slot.val)) =
      lineWeightAt xScale xOut (deferred + 2) fibre := by
  unfold dualWeightFoldValue lineWeightAt exactRaw
  simp_rw [naturalLineValue_four_mul_add]
  rw [scaleExact, xExact, sourceQm31ToModel_mul,
    mappedLineBatchFoldNumerator, doubledTwice_eq_doubledFactorTwo]
  have twoNonzero : (2 : ModelQM31) ≠ 0 := by decide
  rw [pow_add]
  norm_num
  simp [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
    Matrix.vecTail]
  field_simp [twoNonzero]

private theorem dualWeightFoldValue_fin_sum
    {count : Nat} (alpha : ModelQM31)
    (weights : Fin count → Fin 4 → ModelQM31) :
    dualWeightFoldValue alpha
        (fun slot => ∑ position, weights position slot) =
      ∑ position, dualWeightFoldValue alpha (weights position) := by
  unfold dualWeightFoldValue
  simp only [div_eq_mul_inv, Finset.mul_sum, add_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]

/-- A completed source loop invariant and its public deferred-counter update
are exactly one K1 dual fold of the complete 16-line component.  The source
execution theorem supplies these two compact premises. -/
theorem lineBatchFoldPrefix_transports_weights_apply
    (rounds : Nat)
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (deferred : Std.U8) (alpha : RawQM31)
    (scalesOut : Slice RawQM31) (xsOut : Slice RawM31)
    (deferredOut : Std.U8)
    (processed : ∀ index, index < 16 →
      generatedQm31ToExact scalesOut.val[index]! =
        generatedQm31ToExact scales.val[index]! *
          lineBatchFoldNumerator (generatedQm31ToExact alpha)
            (generatedM31ToExact xs.val[index]!) ∧
      generatedM31ToExact xsOut.val[index]! =
        doubledM31 (doubledM31
          (generatedM31ToExact xs.val[index]!)))
    (deferredExact : deferredOut.val = deferred.val + 2)
    (fibre : Fin (radix4Size rounds)) :
    dualWeightFoldLayer (radix4Size rounds) (exactRaw alpha)
        (lineBatchComponentWeights (rounds + 1) scales xs deferred.val)
        fibre =
      lineBatchComponentWeights rounds scalesOut xsOut deferredOut.val
        fibre := by
  unfold dualWeightFoldLayer lineBatchComponentWeights
  simp only [childIndex_val]
  change dualWeightFoldValue (exactRaw alpha)
      (fun slot => ∑ position : Fin 16,
        lineWeightAt scales.val[position.val]! xs.val[position.val]!
          deferred.val (4 * fibre.val + slot.val)) =
    ∑ position : Fin 16,
      lineWeightAt scalesOut.val[position.val]! xsOut.val[position.val]!
        deferredOut.val fibre.val
  rw [deferredExact]
  rw [dualWeightFoldValue_fin_sum]
  apply Finset.sum_congr rfl
  intro position _
  have entry := processed position.val position.isLt
  exact dualWeightFoldValue_lineWeightAt
    scales.val[position.val]! scalesOut.val[position.val]!
    xs.val[position.val]! xsOut.val[position.val]! alpha deferred.val
    fibre.val entry.1 entry.2

theorem lineBatchFoldPrefix_transports_weights
    (rounds : Nat)
    (scales : Slice RawQM31) (xs : Slice RawM31)
    (deferred : Std.U8) (alpha : RawQM31)
    (scalesOut : Slice RawQM31) (xsOut : Slice RawM31)
    (deferredOut : Std.U8)
    (processed : ∀ index, index < 16 →
      generatedQm31ToExact scalesOut.val[index]! =
        generatedQm31ToExact scales.val[index]! *
          lineBatchFoldNumerator (generatedQm31ToExact alpha)
            (generatedM31ToExact xs.val[index]!) ∧
      generatedM31ToExact xsOut.val[index]! =
        doubledM31 (doubledM31
          (generatedM31ToExact xs.val[index]!)))
    (deferredExact : deferredOut.val = deferred.val + 2) :
    dualWeightFoldLayer (radix4Size rounds) (exactRaw alpha)
        (lineBatchComponentWeights (rounds + 1) scales xs deferred.val) =
      lineBatchComponentWeights rounds scalesOut xsOut deferredOut.val := by
  funext fibre
  exact lineBatchFoldPrefix_transports_weights_apply rounds scales xs deferred
    alpha scalesOut xsOut deferredOut processed deferredExact fibre

#print axioms lineBatchFoldPrefix_transports_weights_apply
#print axioms lineBatchFoldPrefix_transports_weights

end V7CallerCurrentReleaseR26K1LineBatchFoldBridge
