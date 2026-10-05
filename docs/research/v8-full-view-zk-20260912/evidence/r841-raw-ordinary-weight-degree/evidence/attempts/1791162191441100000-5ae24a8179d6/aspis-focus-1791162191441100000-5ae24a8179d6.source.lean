import Mathlib.Algebra.MvPolynomial.CommRing
import AspisV8R19.R738JointObservationModel
import AspisV8R19.R839SourceOriginalWeightDegree
import AspisV8R19.R838SourceWeightDegree

/-! Degree bound for the full ordinary source quotient weight, including every image update. -/
set_option autoImplicit false
namespace AspisV8R19.R841RawOrdinaryWeightDegree
open MvPolynomial
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R838SourceWeightDegree
open AspisV8R19.R839SourceOriginalWeightDegree
noncomputable section

variable {F : Type*} [Field F]

lemma raw_ordinary_original_degree (i : Fin 1024) :
    (rawOrdinaryOriginal (pZ (F := F)) (pKappa (F := F)) i).totalDegree ≤ 58 := by
  unfold rawOrdinaryOriginal
  exact ordinary_sourceOriginalWeight_degree (F := F) TwoSwapSourceTable.inactive (fun _ => 0) i

lemma raw_ordinary_transport_degree (j : Fin 1024) :
    (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
      (rawOrdinaryOriginal (pZ (F := F)) (pKappa (F := F))) j).totalDegree ≤ 58 := by
  unfold transportDual
  split
  · exact (totalDegree_sub _ _).trans
      (max_le (raw_ordinary_original_degree (F := F) (TwoSwapSourceTable.order j))
        (raw_ordinary_original_degree (F := F) 1023))
  · exact raw_ordinary_original_degree (F := F) (TwoSwapSourceTable.order j)

lemma raw_ordinary_extend_degree (n : Nat) :
    (extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
      (rawOrdinaryOriginal (pZ (F := F)) (pKappa (F := F)))) n).totalDegree ≤ 58 := by
  unfold extendFin1024
  split
  · exact raw_ordinary_transport_degree (F := F) _
  · simp

lemma abc_degree (l : Fin 3) :
    (polynomialABC (F := F) l).totalDegree ≤ 2 := by
  have hmul : ((pU (F := F) * pV (F := F))).totalDegree ≤ 2 := by
    unfold pU pV
    simpa using totalDegree_mul (X (1 : Fin 15) : JointPoly F) (X 2)
  unfold polynomialABC
  fin_cases l
  · exact (totalDegree_add _ _).trans (max_le (by simp) hmul)
  · exact (totalDegree_sub _ _).trans (max_le hmul (by simp))
  · rw [totalDegree_neg]
    exact (totalDegree_add _ _).trans (by simp)

lemma pTau_degree : (pTau (F := F)).totalDegree ≤ 1 := by
  unfold pTau
  simp

lemma pTau_pow_degree (e : Nat) : ((pTau (F := F)) ^ e).totalDegree ≤ e := by
  exact (totalDegree_pow _ _).trans (by
    simpa [Nat.mul_one] using Nat.mul_le_mul_left e (pTau_degree (F := F)))

lemma raw_chord_transpose_degree (half : F) (i : Nat) :
    (sourceChordTranspose (C (half : F))
      (extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
        (rawOrdinaryOriginal (pZ (F := F)) (pKappa (F := F)))))
      (polynomialABC (F := F) 0) (polynomialABC (F := F) 1) (polynomialABC (F := F) 2) i).totalDegree ≤ 60 := by
  exact (sourceChordTranspose_degree (F := F) half _ _ _ _ 58 2
    (raw_ordinary_extend_degree (F := F)) (abc_degree (F := F) 0)
    (abc_degree (F := F) 1) (abc_degree (F := F) 2) i).trans (by omega)

theorem raw_ordinary_weight_degree (half : F) (i : Nat) :
    (rawOrdinaryWeight (C half) (polynomialABC (F := F) 0)
      (polynomialABC (F := F) 1) (polynomialABC (F := F) 2)
      (pKappa (F := F)) (pTau (F := F)) (pZ (F := F)) i).totalDegree ≤ 60 := by
  unfold rawOrdinaryWeight sourceQuotientWeights
  rw [sourceImageUpdates_apply]
  simp only [Bool.false_eq_true, if_false]
  have hmain := raw_chord_transpose_degree (F := F) half i
  have ht : (pTau (F := F)).totalDegree ≤ 60 := (pTau_degree (F := F)).trans (by omega)
  have htb : ((pTau (F := F)) ^ 2 * polynomialABC (F := F) 1).totalDegree ≤ 60 := by
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add (pTau_pow_degree (F := F) 2) (abc_degree (F := F) 1)) |>.trans (by omega)
  have htc : ((pTau (F := F)) ^ 2 * polynomialABC (F := F) 2).totalDegree ≤ 60 := by
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add (pTau_pow_degree (F := F) 2) (abc_degree (F := F) 2)) |>.trans (by omega)
  have hu1 : ((if i = 1023 then pTau (F := F) else 0)).totalDegree ≤ 60 := by split <;> simp [ht]
  have hu2 : ((if i = 1022 then pTau (F := F) ^ 2 * polynomialABC (F := F) 1 else 0)).totalDegree ≤ 60 := by split <;> simp [htb]
  have hu3 : ((if i = 1021 then pTau (F := F) ^ 2 * polynomialABC (F := F) 2 else 0)).totalDegree ≤ 60 := by split <;> simp [htc]
  exact (totalDegree_sub _ _).trans
    (max_le ((totalDegree_add _ _).trans
      (max_le ((totalDegree_add _ _).trans (max_le hmain hu1)) hu2)) hu3)

#print axioms raw_ordinary_original_degree
#print axioms raw_ordinary_transport_degree
#print axioms raw_ordinary_extend_degree
#print axioms raw_chord_transpose_degree
#print axioms raw_ordinary_weight_degree
end
end AspisV8R19.R841RawOrdinaryWeightDegree
