import AspisV8R19.R684FullSourceMomentIdentity
import AspisV8R19.R678ArbitraryPointResidualRepair
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R685FullJointGImage
open AspisR19 AspisV8R16 AspisV8R17 HighRepairInvariant
open R574SparseGCorePolynomial R645TwoSwapHighDirections R680CoreQuotientSupport
open R660FullSourceResidualCorrection R661TwoSwapMaskAddition R662FullIndexedMaskPreservation
open R649TwoSwapResidualRepair
open BetaUniformCorrection
open R678ArbitraryPointResidualRepair R681FullCoreCoinImage R682FullQueryNormalization
open R683QueryCoreCoinImage R684FullSourceMomentIdentity
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]

theorem extend_correction_at (s : Index 32 → F) (d : Fin 256) (slot : Fin 4) :
    extendCorrection s (d,slot) = if h : d.val < 32 then s (⟨d.val,h⟩,slot) else 0 := by
  change NormalizedGCore.flatten s (4*d.val+slot.val) = _
  unfold NormalizedGCore.flatten
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
  obtain ⟨x,hcorecoins,hcorefold,hcorebalance⟩ :=
    full_core_coin_image half alpha a b c coinsTarget hcore
  obtain ⟨q0,hquery0,hfold0,hsame⟩ :=
    full_query_normalization (coreQuotient alpha x) alpha t ht hcorefold
  have hcoins0 (i : Fin 271) :
      actualCoin (indexedMask half a b c q0) i = coinsTarget i := by
    rw [core_high_coin half alpha a b c x q0 hsame,← core_coin]
    exact hcorecoins i
  have hbalance0 : (∑ r ∈ TwoSwapSourceTable.inactive,
      indexedMask half a b c q0 r) = 0 :=
    core_high_balance half alpha a b c x q0 hsame
  have htail (r : Nat) (hr : 940 ≤ r) : flattenFull q0 r = 0 := by
    rw [flatten_same_high q0 (coreQuotient alpha x) hsame r (by omega),core_flatten]
    exact weightedQ_support alpha x r hr
  have htail1021 : flattenFull q0 1021 = 0 := htail 1021 (by omega)
  have htail1022 : flattenFull q0 1022 = 0 := htail 1022 (by omega)
  have htail1023 : flattenFull q0 1023 = 0 := htail 1023 (by omega)
  have hpair0 : (∑ r : Fin 1024,
      TwoSwapSourceG.original (SourceGConstant.finishCoins half previous) r *
        indexedMask half a b c q0 r) =
      ∑ i : Fin 271, SourceGConstant.finishCoins half previous i * coinsTarget i := by
    rw [R561.original_pairing]
    apply Finset.sum_congr rfl
    intro i _
    change SourceGConstant.finishCoins half previous i *
      actualCoin (indexedMask half a b c q0) i = _
    rw [hcoins0]
  have hboundary0R : fullRelation half quarter a b c kappa tau z previous false q0 0 +
      fullRelation half quarter a b c kappa tau z previous false q0 4 =
      quarter*(kappa*sourcePointFunctional (SourceStatementPoints.points z 0) (indexedMask half a b c q0)+
        kappa^2*sourcePointFunctional (SourceStatementPoints.points z 1) (indexedMask half a b c q0)+
        kappa^3*sourcePointFunctional (SourceStatementPoints.points z 2) (indexedMask half a b c q0)) := by
    rw [full_source_moment_identity]
    simp only [Bool.false_eq_true,ite_false,hbalance0,htail1021,htail1022,htail1023,
      mul_zero,sub_zero,add_zero]
  have hboundary0G : fullRelation half quarter a b c kappa tau z previous true q0 0 +
      fullRelation half quarter a b c kappa tau z previous true q0 4 =
      quarter*(kappa*(∑ i : Fin 271, SourceGConstant.finishCoins half previous i*coinsTarget i)+
        kappa^2*sourcePointFunctional (SourceStatementPoints.points z 1) (indexedMask half a b c q0)+
        kappa^3*sourcePointFunctional (SourceStatementPoints.points z 2) (indexedMask half a b c q0)) := by
    rw [full_source_moment_identity]
    simp only [ite_true,hpair0,hbalance0,htail1021,htail1022,htail1023,
      mul_zero,sub_zero,add_zero]
  let desired : Fin 7 → F := fun k => ordinaryTarget k-
    fullRelation half quarter a b c kappa tau z previous false q0 k.val
  let desiredG : Fin 7 → F := fun k => structuredTarget k-
    fullRelation half quarter a b c kappa tau z previous true q0 k.val
  let points : Fin 3 → F := fun i => pointsTarget i-
    sourcePointFunctional (SourceStatementPoints.points z i) (indexedMask half a b c q0)
  have hrel0R := full_relation_eval_zero half quarter a b c kappa tau alpha z previous false q0 hfold0
  have hrel0G := full_relation_eval_zero half quarter a b c kappa tau alpha z previous true q0 hfold0
  have hdeval : R652ResidualCoefficientCompletion.evalSeven desired alpha = 0 := by
    unfold desired R652ResidualCoefficientCompletion.evalSeven
    simp only [sub_mul,Finset.sum_sub_distrib]
    change R652ResidualCoefficientCompletion.evalSeven ordinaryTarget alpha -
      R652ResidualCoefficientCompletion.evalSeven (fun k : Fin 7 =>
        fullRelation half quarter a b c kappa tau z previous false q0 k.val) alpha = 0
    rw [hordinaryeval,hrel0R,sub_self]
  have hdGeval : R652ResidualCoefficientCompletion.evalSeven desiredG alpha = 0 := by
    unfold desiredG R652ResidualCoefficientCompletion.evalSeven
    simp only [sub_mul,Finset.sum_sub_distrib]
    change R652ResidualCoefficientCompletion.evalSeven structuredTarget alpha -
      R652ResidualCoefficientCompletion.evalSeven (fun k : Fin 7 =>
        fullRelation half quarter a b c kappa tau z previous true q0 k.val) alpha = 0
    rw [hstructuredeval,hrel0G,sub_self]
  have hdboundary : desired 0 + desired 4 =
      quarter*(kappa*points 0+kappa^2*points 1+kappa^3*points 2) := by
    unfold desired points
    change (ordinaryTarget 0-fullRelation half quarter a b c kappa tau z previous false q0 0) +
      (ordinaryTarget 4-fullRelation half quarter a b c kappa tau z previous false q0 4) = _
    linear_combination hordinaryboundary-hboundary0R
  have hdGboundary : desiredG 0 + desiredG 4 =
      quarter*(kappa^2*points 1+kappa^3*points 2) := by
    unfold desiredG points
    change (structuredTarget 0-fullRelation half quarter a b c kappa tau z previous true q0 0) +
      (structuredTarget 4-fullRelation half quarter a b c kappa tau z previous true q0 4) = _
    linear_combination hstructuredboundary-hboundary0G
  obtain ⟨xrepair,hsR,hsG,hspoints,hscoins,hsqueries,hsfold,hsbalance⟩ :=
    arbitrary_point_residual_pair_repair t ht noneOne half quarter a b c kappa alpha tau z previous
      desired desiredG points hquarter hkappa hdeval hdGeval hdboundary hdGboundary hresidual
  let corr := combination t ht noneOne alpha xrepair
  refine ⟨fun i => q0 i+extendCorrection corr i,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [indexed_sparse_coins_preserved t ht noneOne half alpha a b c xrepair q0 i]
    exact hcoins0 i
  · intro i
    unfold sourcePointFunctional
    simp only [indexed_mask_add_correction,mul_add,Finset.sum_add_distrib]
    change sourcePointFunctional (SourceStatementPoints.points z i) (indexedMask half a b c q0) +
      sourcePointFunctional (SourceStatementPoints.points z i) (actualMask half a b c corr) = pointsTarget i
    rw [hspoints]
    unfold points
    ring
  · intro k
    have hc : fullRelation half quarter a b c kappa tau z previous false (extendCorrection corr) k.val = desired k := by
      rw [full_extension_relation]
      exact hsR k
    have hadd := coefficient_left (sourceKernel 256 k.val quarter) q0 (extendCorrection corr)
      (fullWeight half a b c kappa tau z previous false) (1:F) (1:F)
    simp only [one_mul] at hadd
    change coefficient (sourceKernel 256 k.val quarter) (fun i => q0 i+extendCorrection corr i)
      (fullWeight half a b c kappa tau z previous false) = ordinaryTarget k
    rw [hadd]
    change fullRelation half quarter a b c kappa tau z previous false q0 k.val +
      fullRelation half quarter a b c kappa tau z previous false (extendCorrection corr) k.val = ordinaryTarget k
    rw [hc]
    unfold desired
    ring
  · intro k
    have hc : fullRelation half quarter a b c kappa tau z previous true (extendCorrection corr) k.val = desiredG k := by
      rw [full_extension_relation]
      exact hsG k
    have hadd := coefficient_left (sourceKernel 256 k.val quarter) q0 (extendCorrection corr)
      (fullWeight half a b c kappa tau z previous true) (1:F) (1:F)
    simp only [one_mul] at hadd
    change coefficient (sourceKernel 256 k.val quarter) (fun i => q0 i+extendCorrection corr i)
      (fullWeight half a b c kappa tau z previous true) = structuredTarget k
    rw [hadd]
    change fullRelation half quarter a b c kappa tau z previous true q0 k.val +
      fullRelation half quarter a b c kappa tau z previous true (extendCorrection corr) k.val = structuredTarget k
    rw [hc]
    unfold desiredG
    ring
  · intro slot root
    have hadd : evaluate256 (fun d => q0 (d,slot)+extendCorrection corr (d,slot)) (t root) =
        evaluate256 (fun d => q0 (d,slot)) (t root) +
          evaluate256 (fun d => extendCorrection corr (d,slot)) (t root) := by
      unfold evaluate256
      simp only [add_mul, Finset.sum_add_distrib]
    rw [hadd]
    rw [hquery0 slot root,evaluate256_extend,hsqueries slot root,add_zero]
  · intro d
    have hadd : R370KernelEvaluation.firstFold 256 alpha (fun i => q0 i+extendCorrection corr i) d =
        R370KernelEvaluation.firstFold 256 alpha q0 d +
          R370KernelEvaluation.firstFold 256 alpha (extendCorrection corr) d := by
      unfold R370KernelEvaluation.firstFold
      simp only [add_mul, Finset.sum_add_distrib]
    rw [hadd,hfold0 d,firstFold_extend_zero alpha corr hsfold d,add_zero]
  · exact indexed_balance_preserved t ht noneOne half alpha a b c xrepair q0 |>.trans hbalance0

#print axioms extend_correction_at
#print axioms firstFold_extend_zero
#print axioms evaluate256_extend
#print axioms full_joint_g_image
end
end AspisV8R19.R685FullJointGImage
