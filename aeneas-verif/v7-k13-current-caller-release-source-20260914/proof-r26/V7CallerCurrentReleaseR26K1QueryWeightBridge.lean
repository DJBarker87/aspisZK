import V7CallerCurrentReleaseR26QueryWeightSemantics
import AspisFormal.K1.V7Tag73BatchedQuerySourceBridge

/-!
# Current R26 query weights in the maintained K1 basis

The source proof and K1 use isomorphic nested quadratic fields, but the two
modules carry separately elaborated quadratic-extension instances.  This file
makes the coordinate map explicit, proves that it preserves the field
operations used by the source, and identifies the source's shifted line batch
with the exact K1 query covector.  No authentication, acceptance, or
query-consistency proposition is assumed here.
-/

set_option autoImplicit false

namespace V7CallerCurrentReleaseR26K1QueryWeightBridge

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26LineBatchFactorLoop
open V7CallerCurrentReleaseR26QueryWeightSemantics
open AspisCircleTensorBinding
open AspisK1.V7Tag73BatchedQuerySourceBridge
open AspisK1.V7Tag73OperationalRelationSourceFacts
open AspisV5ComponentCQM31TowerExact

abbrev SourceM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev SourceCM31 := V7CallerCurrentReleaseR26FieldBridge.ExactCM31
abbrev SourceQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31
abbrev ModelM31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ModelCM31 := AspisV5ComponentCQM31TowerExact.CM31Exact
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

/-- Coordinate-preserving transport from the R26 quadratic extension to the
maintained K1 quadratic extension. -/
def sourceCm31ToModel (x : SourceCM31) : ModelCM31 := ⟨x.re, x.im⟩

/-- Coordinate-preserving transport for the outer quadratic extension. -/
def sourceQm31ToModel (x : SourceQM31) : ModelQM31 :=
  ⟨sourceCm31ToModel x.re, sourceCm31ToModel x.im⟩

@[simp] theorem sourceCm31ToModel_zero :
    sourceCm31ToModel 0 = 0 := by
  rfl

@[simp] theorem sourceCm31ToModel_one :
    sourceCm31ToModel 1 = 1 := by
  rfl

@[simp] theorem sourceCm31ToModel_add (x y : SourceCM31) :
    sourceCm31ToModel (x + y) =
      sourceCm31ToModel x + sourceCm31ToModel y := by
  ext <;> rfl

@[simp] theorem sourceCm31ToModel_mul (x y : SourceCM31) :
    sourceCm31ToModel (x * y) =
      sourceCm31ToModel x * sourceCm31ToModel y := by
  ext <;> simp [sourceCm31ToModel]

@[simp] theorem sourceQm31ToModel_zero :
    sourceQm31ToModel 0 = 0 := by
  rfl

@[simp] theorem sourceQm31ToModel_one :
    sourceQm31ToModel 1 = 1 := by
  rfl

@[simp] theorem sourceQm31ToModel_add (x y : SourceQM31) :
    sourceQm31ToModel (x + y) =
      sourceQm31ToModel x + sourceQm31ToModel y := by
  ext <;> rfl

@[simp] theorem sourceQm31ToModel_sub (x y : SourceQM31) :
    sourceQm31ToModel (x - y) =
      sourceQm31ToModel x - sourceQm31ToModel y := by
  rfl

@[simp] theorem sourceQm31ToModel_mul (x y : SourceQM31) :
    sourceQm31ToModel (x * y) =
      sourceQm31ToModel x * sourceQm31ToModel y := by
  rfl

/-- The coordinate transport packaged as a ring homomorphism, so finite sums,
products, and powers can be moved into the maintained K1 field symbolically. -/
def sourceQm31ToModelHom : SourceQM31 →+* ModelQM31 where
  toFun := sourceQm31ToModel
  map_zero' := sourceQm31ToModel_zero
  map_one' := sourceQm31ToModel_one
  map_add' := sourceQm31ToModel_add
  map_mul' := sourceQm31ToModel_mul

@[simp] theorem sourceQm31ToModelHom_apply (x : SourceQM31) :
    sourceQm31ToModelHom x = sourceQm31ToModel x := rfl

/-- The literal scalar embedding used by the R26 line evaluator. -/
def sourceEmbedM31 (x : SourceM31) : SourceQM31 := ⟨⟨x, 0⟩, 0⟩

/-- The corresponding scalar embedding in the maintained K1 field. -/
def modelEmbedM31 (x : ModelM31) : ModelQM31 := ⟨⟨x, 0⟩, 0⟩

@[simp] theorem modelEmbedM31_eq_algebraMap (x : ModelM31) :
    modelEmbedM31 x = algebraMap ModelM31 ModelQM31 x := by
  rfl

@[simp] theorem sourceQm31ToModel_sourceEmbedM31 (x : SourceM31) :
    sourceQm31ToModel (sourceEmbedM31 x) = modelEmbedM31 x := by
  rfl

/-- Repeated `2x²-1` commutes with the maintained scalar embedding. -/
theorem embedded_lineFactor_eq_doubledFactor (x : SourceM31) :
    ∀ coordinate,
      modelEmbedM31 (lineFactor x coordinate) =
        doubledFactor (algebraMap ModelM31 ModelQM31 x) coordinate
  | 0 => by simp [lineFactor, doubledFactor]
  | coordinate + 1 => by
      rw [lineFactor, doubledFactor, modelEmbedM31_eq_algebraMap]
      simp only [map_ofNat, map_sub, map_mul, map_pow, map_one]
      rw [← modelEmbedM31_eq_algebraMap,
        embedded_lineFactor_eq_doubledFactor x coordinate]

/-- The source-side bit-product maps exactly to the maintained natural-line
basis value at the embedded M31 coordinate. -/
theorem exactNaturalLineValue_eq_model
    (x : SourceM31) (coefficient : Nat) :
    sourceQm31ToModel (exactNaturalLineValue x coefficient) =
      naturalLineValue (algebraMap ModelM31 ModelQM31 x) coefficient := by
  classical
  change sourceQm31ToModelHom
      (∏ coordinate ∈ coefficient.bitIndices.toFinset,
        sourceEmbedM31 (lineFactor x coordinate)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro coordinate _
  rw [sourceQm31ToModelHom_apply,
    sourceQm31ToModel_sourceEmbedM31,
    embedded_lineFactor_eq_doubledFactor]

/-- Once the source coordinate array is identified with the query schedule,
the exact R26 line-batch evaluator maps to the K1 shifted q16 covector. -/
theorem exactShiftedLineBatchWeight_eq_model
    (queries : Fin 16 → Fin 262144) (rho : SourceQM31)
    (lineX : Nat → SourceM31)
    (lineXExact : ∀ ordinal : Fin 16,
      lineX ordinal.val =
        AspisV7ExactOneFoldDomains.storedFirstLineX18 (queries ordinal))
    (coefficient : Fin 256) :
    sourceQm31ToModel
        (exactShiftedLineBatchWeight rho lineX coefficient.val) =
      exactShiftedQueryBatchWeights queries (sourceQm31ToModel rho)
        coefficient := by
  classical
  rw [exactShiftedQueryBatchWeights_eq_sum]
  change sourceQm31ToModelHom
      (∑ ordinal ∈ Finset.range 16,
        rho ^ (ordinal + 1) * exactNaturalLineValue (lineX ordinal)
          coefficient.val) = _
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro ordinal _
  rw [map_mul, map_pow]
  simp only [sourceQm31ToModelHom_apply]
  rw [exactNaturalLineValue_eq_model,
    lineXExact ordinal]
  rfl

#print axioms sourceCm31ToModel_mul
#print axioms sourceQm31ToModel_mul
#print axioms embedded_lineFactor_eq_doubledFactor
#print axioms exactNaturalLineValue_eq_model
#print axioms exactShiftedLineBatchWeight_eq_model

end V7CallerCurrentReleaseR26K1QueryWeightBridge
