import AspisV8R19.R684FullSourceMomentIdentity
import AspisV8R19.R678ArbitraryPointResidualRepair
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R685FullJointGImage
open AspisR19 AspisV8R16 AspisV8R17 HighRepairInvariant
open R660FullSourceResidualCorrection R661TwoSwapMaskAddition R662FullIndexedMaskPreservation
open R678ArbitraryPointResidualRepair R681FullCoreCoinImage R682FullQueryNormalization
open R683QueryCoreCoinImage R684FullSourceMomentIdentity
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]

theorem extend_correction_at (s : Index 32 → F) (d : Fin 256) (slot : Fin 4) :
    extendCorrection s (d,slot) = if h : d.val < 32 then s (⟨d.val,h⟩,slot) else 0 := by
  unfold extendCorrection NormalizedGCore.flatten
  by_cases hd : d.val < 32
  · rw [dif_pos (by omega), dif_pos hd]
    congr 1
    apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
  · rw [dif_neg (by omega), dif_neg hd]

theorem firstFold_extend_zero (alpha : F) (s : Index 32 → F)
    (hs : ∀ d, R370KernelEvaluation.firstFold 32 alpha s d = 0)
    (d : Fin 256) :
    R370KernelEvaluation.firstFold 256 alpha (extendCorrection s) d = 0 := by
  unfold R370KernelEvaluation.firstFold
  simp_rw [extend_correction_at]
  by_cases hd : d.val < 32
  · simp only [dif_pos hd]
    simpa only [R370KernelEvaluation.firstFold] using hs ⟨d.val,hd⟩
  · simp only [dif_neg hd, zero_mul, Finset.sum_const_zero]

theorem evaluate256_extend (s : Index 32 → F) (slot : Fin 4) (y : F) :
    evaluate256 (fun d => extendCorrection s (d,slot)) y =
      NormalizedQuerySection.evaluate (fun d => s (d,slot)) y := by
  unfold evaluate256 NormalizedQuerySection.evaluate
  rw [Fin.sum_univ_add (a:=32) (b:=224)]
  simp_rw [extend_correction_at]
  simp [Fin.castAdd, Fin.natAdd, Fin.castLE]

/-- Conditional full-dimensional image for the selected field-model G observables.
The theorem is after fixed challenges and does not supply legal-witness,
commitment chronology, oracle, privacy, or security premises. -/
theorem full_joint_g_image (half quarter a b c kappa alpha tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (hquarter : quarter ≠ 0) (hkappa : kappa ≠ 0)
    (hcore : (coreMatrix half alpha a b c).det ≠ 0)
    (hresidual : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
      previous t ht noneOne).det ≠ 0)
    (coinsTarget : Fin 271 → F) (pointsTarget : Fin 3 → F)
    (ordinaryTarget structuredTarget : Fin 7 → F)
    (hordinaryeval : R652ResidualCoefficientCompletion.evalSeven ordinaryTarget alpha = 0)
    (hstructuredeval : R652ResidualCoefficientCompletion.evalSeven structuredTarget alpha = 0)
    (hordinaryboundary : ordinaryTarget 0 + ordinaryTarget 4 =
      quarter*(kappa*pointsTarget 0+kappa^2*pointsTarget 1+kappa^3*pointsTarget 2))
    (hstructuredboundary : structuredTarget 0 + structuredTarget 4 =
      quarter*(kappa*(∑ i : Fin 271, SourceGConstant.finishCoins half previous i*coinsTarget i)+
        kappa^2*pointsTarget 1+kappa^3*pointsTarget 2)) :
    ∃ q : Index 256 → F,
      (∀ i : Fin 271, actualCoin (indexedMask half a b c q) i = coinsTarget i) ∧
      (∀ i : Fin 3, sourcePointFunctional (SourceStatementPoints.points z i)
        (indexedMask half a b c q) = pointsTarget i) ∧
      (∀ k : Fin 7, fullRelation half quarter a b c kappa tau z previous false q k.val = ordinaryTarget k) ∧
      (∀ k : Fin 7, fullRelation half quarter a b c kappa tau z previous true q k.val = structuredTarget k) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22, evaluate256 (fun d => q (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 256, R370KernelEvaluation.firstFold 256 alpha q d = 0) ∧
      (∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c q r) = 0 := by
  obtain ⟨q0,hcoins0,hquery0,hfold0,hbalance0⟩ :=
    query_core_coin_image half alpha a b c coinsTarget t ht hcore
  sorry

#print axioms extend_correction_at
#print axioms firstFold_extend_zero
#print axioms evaluate256_extend
#print axioms full_joint_g_image
end
end AspisV8R19.R685FullJointGImage
