import AspisV8R19.R869NormalizedSemanticCoins
import AspisV8R19.R873SemanticMaskWeightHom
import AspisV8R19.R742SourceObservationHom

set_option autoImplicit false
namespace AspisV8R19.R874SemanticCoinEmbedding
open AspisV8R17 AspisR19 HighRepairInvariant
open AspisR19.R645TwoSwapHighDirections
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R19.R869NormalizedSemanticCoins
open AspisV8R19.R873SemanticMaskWeightHom
open AspisV8R19.R742SourceObservationHom
open scoped BigOperators
noncomputable section
variable {F K : Type*} [Field F] [Field K] [NeZero (2 : F)] [NeZero (2 : K)]

theorem map_coinWeight (f : F →+* K) (half a b c : F) (i : Fin 271) (x : Index 256) :
    f (coinWeight half a b c i x) = coinWeight (f half) (f a) (f b) (f c) i x := by
  unfold coinWeight
  rw [map_sourceChordTranspose]
  have hu : (fun j => f (unitVector (TwoSwapSourceG.coinIndex i).val j)) =
      (unitVector (TwoSwapSourceG.coinIndex i).val : Nat → K) := by
    funext j
    unfold unitVector
    split <;> simp only [map_one, map_zero]
  rw [hu]

theorem map_actualCoin (f : F →+* K) (half a b c : F) (q : Index 256 → F) (i : Fin 271) :
    f (actualCoin (indexedMask half a b c q) i) =
      actualCoin (indexedMask (f half) (f a) (f b) (f c) (fun x => f (q x))) i := by
  rw [actualCoin_contraction, actualCoin_contraction, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_mul, map_coinWeight]

theorem map_weighted_actualCoin (f : F →+* K) (half a b c : F)
    (previous : Fin 271 → F) (q : Index 256 → F) :
    f (∑ i : Fin 271, previous i * actualCoin (indexedMask half a b c q) i) =
      ∑ i : Fin 271, f (previous i) *
        actualCoin (indexedMask (f half) (f a) (f b) (f c) (fun x => f (q x))) i := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_actualCoin]

theorem map_semantic_pairing (f : F →+* K) (half a b c : F)
    (z : RoundCoins F 10) (q : Index 256 → F) :
    f (∑ i : Fin 271, maskWeights271 half z i * actualCoin (indexedMask half a b c q) i) =
      ∑ i : Fin 271, maskWeights271 (f half) (mapCoins f 10 z) i *
        actualCoin (indexedMask (f half) (f a) (f b) (f c) (fun x => f (q x))) i := by
  rw [map_weighted_actualCoin]
  simp only [map_maskWeights271]

#print axioms map_coinWeight
#print axioms map_actualCoin
#print axioms map_weighted_actualCoin
#print axioms map_semantic_pairing
end
end AspisV8R19.R874SemanticCoinEmbedding
