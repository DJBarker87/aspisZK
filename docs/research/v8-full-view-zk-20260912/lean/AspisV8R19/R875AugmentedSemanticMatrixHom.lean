import AspisV8R19.R874SemanticCoinEmbedding
import AspisV8R19.R792JointSourceMatrixHom

/-! Ring-hom naturality of the actual 223-entry source-observation model. -/
set_option autoImplicit false
namespace AspisV8R19.R875AugmentedSemanticMatrixHom
open AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R792JointSourceMatrixHom
open AspisV8R19.R873SemanticMaskWeightHom
open AspisV8R19.R874SemanticCoinEmbedding
open scoped BigOperators
noncomputable section
variable {F K : Type*} [Field F] [Field K] [NeZero (2 : F)] [NeZero (2 : K)]

abbrev Obs := R746SelectedJointMinor.ObservationRow

def semanticEntry (half a b c : F) (z : RoundCoins F 10)
    (q : R738JointObservationModel.Index256 → F) : F :=
  ∑ i : Fin 271, maskWeights271 half z i *
    AspisR19.R645TwoSwapHighDirections.actualCoin
      (AspisV8R19.R662FullIndexedMaskPreservation.indexedMask half a b c q) i

def augmentedMatrix (half quarter alpha u v kappa tau : F) (z : Fin 10 → F)
    (coins : RoundCoins F 10) : Matrix (Obs ⊕ Unit) (Obs ⊕ Unit) F :=
  Matrix.fromBlocks
    (chosenSourceMatrix half quarter alpha u v kappa tau z)
    (fun r (_ : Unit) => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
      (indexedDirection alpha 96 0) r)
    (fun (_ : Unit) c => semanticEntry half (1+u*v) (u*v-1) (-(u+v)) coins
      (indexedDirection alpha (selectedColumns c).1 (selectedColumns c).2))
    (fun (_ : Unit) (_ : Unit) => semanticEntry half (1+u*v) (u*v-1) (-(u+v)) coins
      (indexedDirection alpha 96 0))

lemma map_indexedBasis (f : F →+* K) (d : Fin 256) (slot : Fin 4)
    (x : R738JointObservationModel.Index256) :
    f (indexedBasis 256 d slot x) = indexedBasis 256 d slot x := by
  unfold indexedBasis
  split <;> simp

lemma map_indexedDirection (f : F →+* K) (alpha : F) (d : Fin 255) (s : Fin 3) :
    (fun x => f (indexedDirection alpha d s x)) = indexedDirection (f alpha) d s := by
  funext x
  simp only [indexedDirection, indexedPair, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, map_sub, map_mul, map_pow, map_indexedBasis]


lemma map_rawObservation_indexedDirection (f : F →+* K)
    (half quarter a b c kappa tau alpha : F) (z : Fin 10 → F)
    (d : Fin 255) (s : Fin 3) (row : Obs) :
    f (rawObservation half quarter a b c kappa tau z (indexedDirection alpha d s) row) =
      rawObservation (f half) (f quarter) (f a) (f b) (f c) (f kappa) (f tau)
        (fun i => f (z i)) (indexedDirection (f alpha) d s) row := by
  rw [rawObservation_indexedDirection, map_sparse_row,
    ← rawObservation_indexedDirection]

lemma map_semanticEntry (f : F →+* K) (half a b c : F)
    (z : RoundCoins F 10) (q : R738JointObservationModel.Index256 → F) :
    f (semanticEntry half a b c z q) =
      semanticEntry (f half) (f a) (f b) (f c) (mapCoins f 10 z) (fun x => f (q x)) := by
  exact map_semantic_pairing f half a b c z q

/-- The generic source-defined 223-entry augmented matrix commutes with every
field ring homomorphism, including its retained semantic coin row. -/
theorem map_augmentedMatrix (f : F →+* K) (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (coins : RoundCoins F 10) :
    f.mapMatrix (augmentedMatrix half quarter alpha u v kappa tau z coins) =
      augmentedMatrix (f half) (f quarter) (f alpha) (f u) (f v) (f kappa) (f tau)
        (fun i => f (z i)) (mapCoins f 10 coins) := by
  unfold augmentedMatrix
  have hA := map_chosen_matrix f half quarter alpha u v kappa tau z
  have htop (r : Obs) :
      f (rawObservation half quarter (1+u*v) (u*v-1) (-(u+v))
        kappa tau z (indexedDirection alpha 96 0) r) =
      rawObservation (f half) (f quarter)
        (1+(f u)*(f v)) ((f u)*(f v)-1) (-((f u)+(f v))) (f kappa) (f tau)
        (fun i => f (z i)) (indexedDirection (f alpha) 96 0) r := by
    rw [map_rawObservation_indexedDirection]
    simp only [map_one, map_mul, map_sub, map_neg, map_add]
  have hbottom (c : Obs) :
      f (semanticEntry half (1+u*v) (u*v-1) (-(u+v)) coins
        (indexedDirection alpha (selectedColumns c).1 (selectedColumns c).2)) =
      semanticEntry (f half) (1+(f u)*(f v)) ((f u)*(f v)-1)
        (-((f u)+(f v))) (mapCoins f 10 coins)
        (indexedDirection (f alpha) (selectedColumns c).1 (selectedColumns c).2) := by
    rw [map_semanticEntry, map_indexedDirection]
    simp only [map_one, map_mul, map_sub, map_neg, map_add]
  have hdelta :
      f (semanticEntry half (1+u*v) (u*v-1) (-(u+v)) coins
        (indexedDirection alpha 96 0)) =
      semanticEntry (f half) (1+(f u)*(f v)) ((f u)*(f v)-1)
        (-((f u)+(f v))) (mapCoins f 10 coins) (indexedDirection (f alpha) 96 0) := by
    rw [map_semanticEntry, map_indexedDirection]
    simp only [map_one, map_mul, map_sub, map_neg, map_add]
  ext row col
  rcases row with r | unit <;> rcases col with c | unit
  · exact congrFun (congrFun hA r) c
  · exact htop r
  · exact hbottom c
  · exact hdelta

theorem map_augmentedMatrix_det (f : F →+* K) (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (coins : RoundCoins F 10) :
    f ((augmentedMatrix half quarter alpha u v kappa tau z coins).det) =
      (augmentedMatrix (f half) (f quarter) (f alpha) (f u) (f v) (f kappa) (f tau)
        (fun i => f (z i)) (mapCoins f 10 coins)).det := by
  classical
  rw [f.map_det, map_augmentedMatrix]

#print axioms map_indexedBasis
#print axioms map_indexedDirection
#print axioms map_rawObservation_indexedDirection
#print axioms map_semanticEntry
#print axioms map_augmentedMatrix
#print axioms map_augmentedMatrix_det
end
end AspisV8R19.R875AugmentedSemanticMatrixHom
