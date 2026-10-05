import AspisV8R19.R868LowSemanticPairing
import AspisV8R19.R767NormalizedSparseEntry
import AspisV8R19.R665FullSourceP2Boundary
import AspisV8R19.R740SparsePointObservation

/-! Query normalization preserves every selected sparse semantic coin. -/
set_option autoImplicit false
namespace AspisV8R19.R869NormalizedSemanticCoins
open AspisR19 AspisV8R16 AspisV8R17 HighRepairInvariant
open AspisR19.TwoSwapSourceTable
open AspisR19.R645TwoSwapHighDirections
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R19.R661TwoSwapMaskAddition
open AspisV8R19.R739AugmentedQuery256
open AspisV8R19.R665FullSourceP2Boundary
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R767NormalizedSparseEntry
open AspisV8R19.R758NormalizedLowRepair
open AspisV8R19.R868LowSemanticPairing
open AspisV8R19.R740SparsePointObservation
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def coinWeight (half a b c : F) (i : Fin 271) : R738JointObservationModel.Index256 → F :=
  fun x => sourceChordTranspose half (unitVector (TwoSwapSourceG.coinIndex i).val) a b c
    (4*x.1.val+x.2.val)

/-- A selected sparse coin is the source-chord transpose contraction against
its exact source index. -/
theorem actualCoin_contraction (half a b c : F) (q : R738JointObservationModel.Index256 → F) (i : Fin 271) :
    actualCoin (indexedMask half a b c q) i =
      ∑ d : Fin 256, ∑ s : Fin 4, q (d,s) * coinWeight half a b c i (d,s) := by
  simp only [actualCoin, indexedMask, fullMask, R562.inverseChordMessage,
    inverseTransport, if_neg (TwoSwapSourceG.coin_not_pivot i), Equiv.symm_apply_apply]
  have h := source_chord_transpose_pairing half (flattenFull q)
    (unitVector (TwoSwapSourceG.coinIndex i).val) a b c
  have hleft : rangeDot 1024 (unitVector (TwoSwapSourceG.coinIndex i).val)
      (sourceChord half (flattenFull q) a b c) =
      sourceChord half (flattenFull q) a b c (TwoSwapSourceG.coinIndex i).val := by
    rw [rangeDot_comm]
    exact rangeDot_unitVector 1024 (TwoSwapSourceG.coinIndex i).val
      (TwoSwapSourceG.coinIndex i).isLt _
  rw [hleft] at h
  rw [h]
  exact full_flatten_pairing q _

lemma normalized_pair_contraction (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (d : Fin 256) (s : Fin 3) (w : R738JointObservationModel.Index256 → F) :
    (∑ i : Fin 256, ∑ slot : Fin 4,
      normalizedPair alpha t ht noneOne d s (i,slot) * w (i,slot)) =
      ((w (d,⟨s.val+1,by omega⟩) - alpha^(s.val+1)*w (d,0)) -
        (w (0,⟨s.val+1,by omega⟩) - alpha^(s.val+1)*w (0,0))) -
      ∑ j : Fin 23, low t ht noneOne d j *
        ((w (⟨j.val,by omega⟩,⟨s.val+1,by omega⟩) -
          alpha^(s.val+1)*w (⟨j.val,by omega⟩,0)) -
        (w (0,⟨s.val+1,by omega⟩) - alpha^(s.val+1)*w (0,0))) := by
  simp only [normalizedPair]
  calc
    _ = ∑ i : Fin 256, normalized t ht noneOne d i *
        (w (i,⟨s.val+1,by omega⟩) - alpha^(s.val+1)*w (i,0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact pair_block (normalized t ht noneOne d i) alpha i s
        (fun slot => w (i,slot))
    _ = _ := normalized_weight_repair t ht noneOne d
      (fun i => w (i,⟨s.val+1,by omega⟩) - alpha^(s.val+1)*w (i,0))

lemma actualCoin_indexedDirection_contraction (half alpha a b c : F)
    (d : Fin 255) (s : Fin 3) (i : Fin 271) :
    actualCoin (indexedMask half a b c (indexedDirection alpha d s)) i =
      (coinWeight half a b c i (cast255 d,⟨s.val+1,by omega⟩) -
        alpha^(s.val+1)*coinWeight half a b c i (cast255 d,0)) -
      (coinWeight half a b c i (0,⟨s.val+1,by omega⟩) -
        alpha^(s.val+1)*coinWeight half a b c i (0,0)) := by
  rw [actualCoin_contraction]
  simp only [indexedDirection, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [pair_contraction, pair_contraction]

/-- Normalization changes no selected sparse coin: its low repair directions
are separately zero on every selected coin. -/
theorem actualCoin_normalizedPair (half alpha a b c : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (d : Fin 255) (s : Fin 3) (i : Fin 271) :
    actualCoin (indexedMask half a b c
      (normalizedPair alpha t ht noneOne (cast255 d) s)) i =
    actualCoin (indexedMask half a b c (indexedDirection alpha d s)) i :=   rw [actualCoin_contraction, normalized_pair_contraction,
    actualCoin_indexedDirection_contraction]
  have hsum : ∑ j : Fin 23, low t ht noneOne (cast255 d) j *
      ((coinWeight half a b c i (⟨j.val,by omega⟩,⟨s.val+1,by omega⟩) -
        alpha^(s.val+1)*coinWeight half a b c i (⟨j.val,by omega⟩,0)) -
      (coinWeight half a b c i (0,⟨s.val+1,by omega⟩) -
        alpha^(s.val+1)*coinWeight half a b c i (0,0))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hz := actual_coin_indexedDirection_zero half alpha a b c j s i
    have hc := actualCoin_indexedDirection_contraction half alpha a b c
      (⟨j.val,by omega⟩ : Fin 255) s i
    rw [hc] at hz
    rw [hz]
    ring
  rw [hsum]
  ring

/-- Therefore every retained 271-coordinate semantic pairing is unchanged. -/
theorem weighted_actualCoin_normalizedPair (half alpha a b c : F)
    (previous : Fin 271 → F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (d : Fin 255) (s : Fin 3) :
    (∑ i : Fin 271, previous i * actualCoin (indexedMask half a b c
      (normalizedPair alpha t ht noneOne (cast255 d) s)) i) =
    (∑ i : Fin 271, previous i * actualCoin (indexedMask half a b c
      (indexedDirection alpha d s)) i) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [actualCoin_normalizedPair]

#print axioms actualCoin_contraction
#print axioms normalized_pair_contraction
#print axioms actualCoin_indexedDirection_contraction
#print axioms actualCoin_normalizedPair
#print axioms weighted_actualCoin_normalizedPair
end
end AspisV8R19.R869NormalizedSemanticCoins
