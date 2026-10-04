import AspisV8R19.R670AllPointResidualRepair
import AspisV8R19.R665FullSourceP2Boundary
set_option autoImplicit false
namespace AspisV8R19.R671WeakMomentResidualRepair
open AspisR19 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open R645TwoSwapHighDirections R649TwoSwapResidualRepair
open R660FullSourceResidualCorrection R662FullIndexedMaskPreservation
open R652ResidualCoefficientCompletion R665FullSourceP2Boundary R670AllPointResidualRepair
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem weak_moment_residual_repair (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half quarter a b c kappa alpha tau scale : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (r g0 : Index 256 → F)
    (hquarter : quarter ≠ 0) (hkappa : kappa ≠ 0) (hscale : scale ≠ 0)
    (hf : ∀ d, R370KernelEvaluation.firstFold 256 alpha r d = 0)
    (hfg : ∀ d, R370KernelEvaluation.firstFold 256 alpha g0 d = 0)
    (hr : ∀ k : Fin 7, fullRelation half quarter a b c kappa tau z previous false r k.val = 0)
    (hgm : (∑ d : Fin 256, ∑ s : Fin 4, g0 (d,s) *
      fullWeight half a b c kappa tau z previous true (d,s)) = 0)
    (hcrossm : (∑ d : Fin 256, ∑ s : Fin 4, r (d,s) *
      fullWeight half a b c kappa tau z previous true (d,s)) + scale *
      (∑ d : Fin 256, ∑ s : Fin 4, g0 (d,s) *
      fullWeight half a b c kappa tau z previous false (d,s)) = 0)
    (hdet : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
      previous t ht noneOne).det ≠ 0) :
    ∃ x : Fin 13 → F,
      (∀ beta : F, ∀ k : Fin 7,
        coefficient (sourceKernel 256 k.val quarter)
          (fun i => (1-beta)*r i + scale*beta*(g0 i + extendCorrection (combination t ht noneOne alpha x) i))
          (fun i => (1-beta)*fullWeight half a b c kappa tau z previous false i +
            beta*fullWeight half a b c kappa tau z previous true i) = 0) ∧
      (scale * (rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true)
        (flattenFull (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j)) -
        rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false)
        (flattenFull (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j))) -
        (rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true) (flattenFull r) -
        rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false) (flattenFull r)) = 0) ∧
      (∀ i : Fin 271, actualCoin (indexedMask half a b c
        (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j)) i =
        actualCoin (indexedMask half a b c g0) i) ∧
      (∀ i : Fin 3, sourcePointFunctional (SourceStatementPoints.points z i)
        (indexedMask half a b c (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j)) =
        sourcePointFunctional (SourceStatementPoints.points z i) (indexedMask half a b c g0)) ∧
      ((∑ v ∈ TwoSwapSourceTable.inactive, indexedMask half a b c
        (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j) v) =
        ∑ v ∈ TwoSwapSourceTable.inactive, indexedMask half a b c g0 v) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22, NormalizedQuerySection.evaluate
        (fun d => combination t ht noneOne alpha x (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 32, R370KernelEvaluation.firstFold 32 alpha
        (combination t ht noneOne alpha x) d = 0) := by
  let desired : Fin 7 → F := fun k => (-scale⁻¹) * fullRelation half quarter a b c kappa tau z previous true r k.val -
    fullRelation half quarter a b c kappa tau z previous false g0 k.val
  let desiredG : Fin 7 → F := fun k => -fullRelation half quarter a b c kappa tau z previous true g0 k.val
  have hd : evalSeven desired alpha = 0 := by
    have he := full_relation_eval_zero half quarter a b c kappa tau alpha z previous true r hf
    have heg := full_relation_eval_zero half quarter a b c kappa tau alpha z previous false g0 hfg
    calc
      evalSeven desired alpha = (-scale⁻¹) * evalSeven
        (fun k : Fin 7 => fullRelation half quarter a b c kappa tau z previous true r k.val) alpha - evalSeven
        (fun k : Fin 7 => fullRelation half quarter a b c kappa tau z previous false g0 k.val) alpha := by
          simp only [evalSeven, desired, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      _ = 0 := by rw [he,heg,mul_zero,sub_self]
  have hdG : evalSeven desiredG alpha = 0 := by
    have he := full_relation_eval_zero half quarter a b c kappa tau alpha z previous true g0 hfg
    simp only [evalSeven, desiredG, Finset.mul_sum]
    rw [he,neg_zero]
  have hbG : desiredG 0 + desiredG 4 = 0 := by
    have h := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter g0
      (fullWeight half a b c kappa tau z previous true)
    change fullRelation half quarter a b c kappa tau z previous true g0 0 +
      fullRelation half quarter a b c kappa tau z previous true g0 4 = _ at h
    rw [hgm,mul_zero] at h
    dsimp [desiredG]
    rw [← neg_add, h]
    simp
  have hb : desired 0 + desired 4 = 0 := by
    have hR := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter r
      (fullWeight half a b c kappa tau z previous true)
    have hG := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter g0
      (fullWeight half a b c kappa tau z previous false)
    change fullRelation half quarter a b c kappa tau z previous true r 0 +
      fullRelation half quarter a b c kappa tau z previous true r 4 = _ at hR
    change fullRelation half quarter a b c kappa tau z previous false g0 0 +
      fullRelation half quarter a b c kappa tau z previous false g0 4 = _ at hG
    have hm : fullRelation half quarter a b c kappa tau z previous true r 0 +
        fullRelation half quarter a b c kappa tau z previous true r 4 + scale *
        (fullRelation half quarter a b c kappa tau z previous false g0 0 +
          fullRelation half quarter a b c kappa tau z previous false g0 4) = 0 := by
      rw [hR,hG]
      have : quarter * ((∑ d : Fin 256, ∑ s : Fin 4, r (d,s)*fullWeight half a b c kappa tau z previous true (d,s)) +
        scale*(∑ d : Fin 256, ∑ s : Fin 4, g0 (d,s)*fullWeight half a b c kappa tau z previous false (d,s))) = 0 := by
        rw [hcrossm,mul_zero]
      convert this using 1 <;> ring
    dsimp [desired]
    have hinv : scale * scale⁻¹ = 1 := mul_inv_cancel₀ hscale
    calc
      (-scale⁻¹ * fullRelation half quarter a b c kappa tau z previous true r 0 -
          fullRelation half quarter a b c kappa tau z previous false g0 0) +
        (-scale⁻¹ * fullRelation half quarter a b c kappa tau z previous true r 4 -
          fullRelation half quarter a b c kappa tau z previous false g0 4) =
        -scale⁻¹ * (fullRelation half quarter a b c kappa tau z previous true r 0 +
          fullRelation half quarter a b c kappa tau z previous true r 4 + scale *
          (fullRelation half quarter a b c kappa tau z previous false g0 0 +
          fullRelation half quarter a b c kappa tau z previous false g0 4)) := by rw [hinv]; ring
      _ = 0 := by rw [hm, mul_zero]
  obtain ⟨x,hO,hG,hpoints,hcoins,hqueries,hfold,hbalance⟩ :=
    all_point_residual_pair_repair t ht noneOne half quarter a b c kappa alpha tau z previous
      desired desiredG hquarter hkappa hd hdG hb hbG hdet
  have hquad : ∀ beta : F, ∀ k : Fin 7,
      coefficient (sourceKernel 256 k.val quarter)
        (fun i => (1-beta)*r i + scale*beta*(g0 i + extendCorrection (combination t ht noneOne alpha x) i))
        (fun i => (1-beta)*fullWeight half a b c kappa tau z previous false i +
          beta*fullWeight half a b c kappa tau z previous true i) = 0 := by
    intro beta k
    apply folded_coefficient_zero
    · exact hr k
    · have hc : fullRelation half quarter a b c kappa tau z previous false
          (extendCorrection (combination t ht noneOne alpha x)) k.val = desired k := by
        rw [full_extension_relation]
        exact hO k
      have hadd := coefficient_left (sourceKernel 256 k.val quarter) g0
        (extendCorrection (combination t ht noneOne alpha x))
        (fullWeight half a b c kappa tau z previous false) (1:F) (1:F)
      simp only [one_mul] at hadd
      rw [hadd]
      change fullRelation half quarter a b c kappa tau z previous true r k.val + scale *
        (fullRelation half quarter a b c kappa tau z previous false g0 k.val +
        fullRelation half quarter a b c kappa tau z previous false (extendCorrection (combination t ht noneOne alpha x)) k.val) = 0
      rw [hc]
      have cancel (v u : F) : v + scale * (u + ((-scale⁻¹)*v-u)) = 0 := by
        rw [show scale*scale⁻¹=1 by exact mul_inv_cancel₀ hscale]
        ring
      exact cancel _ _
    · have hg : fullRelation half quarter a b c kappa tau z previous true
          (extendCorrection (combination t ht noneOne alpha x)) k.val = desiredG k := by
        rw [full_extension_relation]
        exact hG k
      have hadd := coefficient_left (sourceKernel 256 k.val quarter) g0
        (extendCorrection (combination t ht noneOne alpha x))
        (fullWeight half a b c kappa tau z previous true) (1:F) (1:F)
      simp only [one_mul] at hadd
      rw [hadd]
      change fullRelation half quarter a b c kappa tau z previous true g0 k.val +
        fullRelation half quarter a b c kappa tau z previous true (extendCorrection (combination t ht noneOne alpha x)) k.val = 0
      rw [hg]
      dsimp [desiredG]
      ring
  refine ⟨x,hquad,?_,?_,?_,?_,hqueries,hfold⟩
  · exact full_source_p2 half quarter a b c kappa tau scale z previous r
      (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j) hquarter hscale hquad
  · exact indexed_sparse_coins_preserved t ht noneOne half alpha a b c x g0
  · intro i
    exact indexed_point_preserved half a b c g0 (combination t ht noneOne alpha x)
      (SourceStatementPoints.points z i) (hpoints i)
  · exact indexed_balance_preserved t ht noneOne half alpha a b c x g0

#print axioms weak_moment_residual_repair
end
end AspisV8R19.R671WeakMomentResidualRepair
