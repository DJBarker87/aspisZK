import V7CallerCurrentReleaseR26MultilinearFoldSemantics
import V7CallerCurrentReleaseR26TensorFoldSemantics
import V7CallerCurrentReleaseR26K1QueryWeightBridge

/-!
# Current structured weight folds in the maintained K1 model

This file gives the compact multilinear and tensor components their complete
radix-four meaning and transports the two source helper proofs into K1
`dualWeightFoldLayer` equalities.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result

namespace V7CallerCurrentReleaseR26K1StructuredWeightBridge

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26MultilinearFoldSemantics
open V7CallerCurrentReleaseR26TensorFoldSemantics
open AspisV5FriRelationCandidateBridge
open AspisV5ComponentCConcreteFoldLinearity

abbrev RawQM31 := V7CallerCurrentReleaseR26.field.QM31
abbrev RawPrepared :=
  V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 :=
  ⟨V7CallerCurrentReleaseR26.field.QM31.ZERO⟩

inductive StructuredWeightKind where
  | multilinear
  | tensor
deriving DecidableEq

def exactRaw (value : RawQM31) : ModelQM31 :=
  sourceQm31ToModel (generatedQm31ToExact value)

@[simp] private theorem sourceQm31ToModel_pow
    (value : V7CallerCurrentReleaseR26FieldBridge.ExactQM31) (power : Nat) :
    sourceQm31ToModel (value ^ power) =
      sourceQm31ToModel value ^ power := by
  change sourceQm31ToModelHom (value ^ power) =
    sourceQm31ToModelHom value ^ power
  exact map_pow sourceQm31ToModelHom value power

@[simp] private theorem sourceQm31ToModel_four :
    sourceQm31ToModel
        (4 : V7CallerCurrentReleaseR26FieldBridge.ExactQM31) =
      (4 : ModelQM31) := by
  change sourceQm31ToModelHom 4 = 4
  exact map_ofNat sourceQm31ToModelHom 4

def structuredPairWeights (kind : StructuredWeightKind)
    (values : List RawQM31) (pair : Nat) : Fin 4 → ModelQM31 :=
  let high := exactRaw values[2 * pair]!
  let low := exactRaw values[2 * pair + 1]!
  match kind with
  | .multilinear =>
      ![(1 - high) * (1 - low), (1 - high) * low,
        high * (1 - low), high * low]
  | .tensor => ![1, low, high, high * low]

def structuredBasisWeightNat (kind : StructuredWeightKind)
    (values : List RawQM31) : Nat → Nat → ModelQM31
  | 0, _ => 1
  | rounds + 1, index =>
      structuredBasisWeightNat kind values rounds (index / 4) *
        structuredPairWeights kind values rounds
          ⟨index % 4, Nat.mod_lt _ (by decide)⟩

def radix4Size : Nat → Nat
  | 0 => 1
  | rounds + 1 => 4 * radix4Size rounds

def structuredComponentWeights (kind : StructuredWeightKind)
    (rounds : Nat) (scale : RawQM31) (values : List RawQM31) :
    Fin (radix4Size rounds) → ModelQM31 :=
  fun index => exactRaw scale *
    structuredBasisWeightNat kind values rounds index.val

private theorem childIndexDivFour {n : Nat}
    (fibre : Fin n) (slot : Fin 4) :
    (childIndex fibre slot).val / 4 = fibre.val := by
  change (4 * fibre.val + slot.val) / 4 = fibre.val
  omega

private theorem childIndexModFour {n : Nat}
    (fibre : Fin n) (slot : Fin 4) :
    (childIndex fibre slot).val % 4 = slot.val := by
  simp [childIndex]

theorem dualWeightFoldLayer_structuredComponentWeights
    (kind : StructuredWeightKind) (rounds : Nat)
    (scale alpha : RawQM31) (values : List RawQM31) :
    dualWeightFoldLayer (radix4Size rounds) (exactRaw alpha)
        (structuredComponentWeights kind (rounds + 1) scale values) =
      fun fibre =>
        structuredComponentWeights kind rounds scale values fibre *
          dualWeightFoldValue (exactRaw alpha)
            (structuredPairWeights kind values rounds) := by
  funext fibre
  unfold dualWeightFoldLayer dualWeightFoldValue
    structuredComponentWeights
  simp only [structuredBasisWeightNat, childIndexDivFour,
    childIndexModFour]
  ring

theorem structuredBasisWeightNat_congr_prefix
    (kind : StructuredWeightKind) (left right : List RawQM31)
    (rounds index : Nat)
    (samePrefix : ∀ position, position < 2 * rounds →
      left[position]! = right[position]!) :
    structuredBasisWeightNat kind left rounds index =
      structuredBasisWeightNat kind right rounds index := by
  induction rounds generalizing index with
  | zero => rfl
  | succ rounds ih =>
      have recursivePrefix : ∀ position, position < 2 * rounds →
          left[position]! = right[position]! := by
        intro position bound
        exact samePrefix position (by omega)
      have recursive := ih (index := index / 4) recursivePrefix
      have highExact : left[2 * rounds]! = right[2 * rounds]! :=
        samePrefix (2 * rounds) (by omega)
      have lowExact : left[2 * rounds + 1]! =
          right[2 * rounds + 1]! :=
        samePrefix (2 * rounds + 1) (by omega)
      have pairExact : structuredPairWeights kind left rounds =
          structuredPairWeights kind right rounds := by
        cases kind <;> funext slot <;>
          simp [structuredPairWeights, highExact, lowExact]
      simp only [structuredBasisWeightNat]
      rw [recursive, pairExact]

theorem structuredBasisWeightNat_take
    (kind : StructuredWeightKind) (values : List RawQM31)
    (rounds index : Nat) :
    structuredBasisWeightNat kind (values.take (2 * rounds)) rounds index =
      structuredBasisWeightNat kind values rounds index := by
  apply structuredBasisWeightNat_congr_prefix
  intro position bound
  simp [List.getElem!_eq_getElem?_getD, bound]

private theorem mappedMultilinearNumerator
    (alpha z0 z1 : V7CallerCurrentReleaseR26FieldBridge.ExactQM31) :
    sourceQm31ToModel
        (multilinearDualNumerator alpha z0 z1) =
      let weights : Fin 4 → ModelQM31 :=
        ![(1 - sourceQm31ToModel z0) * (1 - sourceQm31ToModel z1),
          (1 - sourceQm31ToModel z0) * sourceQm31ToModel z1,
          sourceQm31ToModel z0 * (1 - sourceQm31ToModel z1),
          sourceQm31ToModel z0 * sourceQm31ToModel z1]
      weights 0 + sourceQm31ToModel alpha ^ 3 * weights 1 +
        sourceQm31ToModel alpha ^ 2 * weights 2 +
        sourceQm31ToModel alpha * weights 3 := by
  simp [multilinearDualNumerator, sourceDualWeightFoldNumerator,
    multilinearFibreWeights]

private theorem mappedTensorNumerator
    (alpha high low : V7CallerCurrentReleaseR26FieldBridge.ExactQM31) :
    sourceQm31ToModel (tensorDualNumerator alpha high low) =
      let weights : Fin 4 → ModelQM31 :=
        ![1, sourceQm31ToModel low, sourceQm31ToModel high,
          sourceQm31ToModel high * sourceQm31ToModel low]
      weights 0 + sourceQm31ToModel alpha ^ 3 * weights 1 +
        sourceQm31ToModel alpha ^ 2 * weights 2 +
        sourceQm31ToModel alpha * weights 3 := by
  simp [tensorDualNumerator, tensorFibreWeights]

theorem fold_multilinear_arity4_transports_weights
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31) (rounds : Nat)
    (hpointLength : point.val.length = 2 * (rounds + 1))
    (hrounds : rounds ≤ 4)
    (hscale : GeneratedCanonicalQM31 scale)
    (hpoint :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        point.val)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (scaleOut : RawQM31) (pointOut : alloc.vec.Vec RawQM31)
    (success :
      V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
        scale point alpha alpha2 alpha3 = ok (scaleOut, pointOut)) :
    GeneratedCanonicalQM31 scaleOut ∧
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        pointOut.val ∧
      pointOut.val.length = 2 * rounds ∧
      dualWeightFoldLayer (radix4Size rounds) (exactRaw alpha)
          (structuredComponentWeights .multilinear (rounds + 1) scale
            point.val) =
        structuredComponentWeights .multilinear rounds scaleOut
          pointOut.val := by
  have pointLength : point.val.length = 2 * rounds + 2 := by omega
  obtain ⟨expectedScale, expectedPoint, factorExact, expectedRun,
      expectedCanonical, expectedPointCanonical, expectedPointExact,
      expectedScaleExact, factorFour⟩ :=
    fold_multilinear_arity4_exact scale point alpha alpha2 alpha3
      (2 * rounds) pointLength (by omega) hscale hpoint halpha halpha2
      halpha3 halpha2Exact halpha3Exact
  rw [success] at expectedRun
  have outputExact : (expectedScale, expectedPoint) =
      (scaleOut, pointOut) := Result.ok.inj expectedRun.symm
  cases outputExact
  refine ⟨expectedCanonical, expectedPointCanonical, ?_, ?_⟩
  · rw [expectedPointExact, List.length_take, hpointLength]
    omega
  · rw [dualWeightFoldLayer_structuredComponentWeights]
    funext fibre
    unfold structuredComponentWeights exactRaw
    rw [expectedPointExact, structuredBasisWeightNat_take,
      expectedScaleExact, sourceQm31ToModel_mul]
    have mappedFour := congrArg sourceQm31ToModel factorFour
    simp only [sourceQm31ToModel_mul, sourceQm31ToModel_four] at mappedFour
    rw [mappedMultilinearNumerator] at mappedFour
    have fourNonzero : (4 : ModelQM31) ≠ 0 := by decide
    have factorMapped : sourceQm31ToModel factorExact =
        dualWeightFoldValue (sourceQm31ToModel
          (generatedQm31ToExact alpha))
          (structuredPairWeights .multilinear point.val rounds) := by
      unfold dualWeightFoldValue structuredPairWeights
      apply (eq_div_iff fourNonzero).2
      simpa [exactRaw] using mappedFour
    rw [factorMapped]
    ring

theorem fold_tensor_arity4_transports_weights
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (rounds : Nat)
    (hfactorsLength : factors.val.length = 2 * (rounds + 1))
    (hrounds : rounds ≤ 4)
    (hscale : GeneratedCanonicalQM31 scale)
    (hfactors : V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      factors.val)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (hpreparedAlpha :
      V7CallerCurrentReleaseR26PreparedSumSemantics.RepresentsPrepared
        preparedAlpha alpha)
    (hpreparedAlpha2 :
      V7CallerCurrentReleaseR26PreparedSumSemantics.RepresentsPrepared
        preparedAlpha2 alpha2)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (scaleOut : RawQM31) (factorsOut : alloc.vec.Vec RawQM31)
    (success :
      V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.fold_tensor_arity4
        scale factors alpha3 preparedAlpha preparedAlpha2 =
          ok (scaleOut, factorsOut)) :
    GeneratedCanonicalQM31 scaleOut ∧
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
        factorsOut.val ∧
      factorsOut.val.length = 2 * rounds ∧
      dualWeightFoldLayer (radix4Size rounds) (exactRaw alpha)
          (structuredComponentWeights .tensor (rounds + 1) scale
            factors.val) =
        structuredComponentWeights .tensor rounds scaleOut
          factorsOut.val := by
  have factorsLength : factors.val.length = 2 * rounds + 2 := by omega
  obtain ⟨expectedScale, expectedFactors, factorExact, expectedRun,
      expectedCanonical, expectedFactorsCanonical, expectedFactorsExact,
      expectedScaleExact, factorFour⟩ :=
    fold_tensor_arity4_exact scale factors alpha alpha2 alpha3
      preparedAlpha preparedAlpha2 (2 * rounds) factorsLength (by omega)
      hscale hfactors halpha halpha2 halpha3 hpreparedAlpha hpreparedAlpha2
      halpha2Exact halpha3Exact
  rw [success] at expectedRun
  have outputExact : (expectedScale, expectedFactors) =
      (scaleOut, factorsOut) := Result.ok.inj expectedRun.symm
  cases outputExact
  refine ⟨expectedCanonical, expectedFactorsCanonical, ?_, ?_⟩
  · rw [expectedFactorsExact, List.length_take, hfactorsLength]
    omega
  · rw [dualWeightFoldLayer_structuredComponentWeights]
    funext fibre
    unfold structuredComponentWeights exactRaw
    rw [expectedFactorsExact, structuredBasisWeightNat_take,
      expectedScaleExact, sourceQm31ToModel_mul]
    have mappedFour := congrArg sourceQm31ToModel factorFour
    simp only [sourceQm31ToModel_mul, sourceQm31ToModel_four] at mappedFour
    rw [mappedTensorNumerator] at mappedFour
    have fourNonzero : (4 : ModelQM31) ≠ 0 := by decide
    have factorMapped : sourceQm31ToModel factorExact =
        dualWeightFoldValue (sourceQm31ToModel
          (generatedQm31ToExact alpha))
          (structuredPairWeights .tensor factors.val rounds) := by
      unfold dualWeightFoldValue structuredPairWeights
      apply (eq_div_iff fourNonzero).2
      simpa [exactRaw] using mappedFour
    rw [factorMapped]
    ring

#print axioms dualWeightFoldLayer_structuredComponentWeights
#print axioms fold_multilinear_arity4_transports_weights
#print axioms fold_tensor_arity4_transports_weights

end V7CallerCurrentReleaseR26K1StructuredWeightBridge
