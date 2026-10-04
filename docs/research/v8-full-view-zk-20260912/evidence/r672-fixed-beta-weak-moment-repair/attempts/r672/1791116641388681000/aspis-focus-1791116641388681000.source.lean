import AspisV8R19.R670AllPointResidualRepair
import AspisV8R19.R665FullSourceP2Boundary
set_option autoImplicit false
namespace AspisV8R19.R672FixedBetaWeakMomentRepair
open AspisR19 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open R645TwoSwapHighDirections R649TwoSwapResidualRepair
open R660FullSourceResidualCorrection R662FullIndexedMaskPreservation
open R652ResidualCoefficientCompletion R665FullSourceP2Boundary R670AllPointResidualRepair
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem fixed_beta_weak_moment_repair (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half quarter a b c kappa alpha tau scale : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (beta : F) (r g0 : Index 256 → F)
    (hquarter : quarter ≠ 0) (hkappa : kappa ≠ 0) (hscale : scale ≠ 0) (hbeta : beta ≠ 0)
    (hf : ∀ d, R370KernelEvaluation.firstFold 256 alpha r d = 0)
    (hfg : ∀ d, R370KernelEvaluation.firstFold 256 alpha g0 d = 0)
    (hrm : (∑ d : Fin 256, ∑ s : Fin 4, r (d,s) *
      fullWeight half a b c kappa tau z previous false (d,s)) = 0)
    (hgm : (∑ d : Fin 256, ∑ s : Fin 4, g0 (d,s) *
      fullWeight half a b c kappa tau z previous true (d,s)) = 0)
    (hcrossm : (∑ d : Fin 256, ∑ s : Fin 4, r (d,s) *
      fullWeight half a b c kappa tau z previous true (d,s)) + scale *
      (∑ d : Fin 256, ∑ s : Fin 4, g0 (d,s) *
      fullWeight half a b c kappa tau z previous false (d,s)) = 0)
    (hdet : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
      previous t ht noneOne).det ≠ 0) :
    ∃ x : Fin 13 → F,
      (∀ k : Fin 7,
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
        (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j)) i = actualCoin (indexedMask half a b c g0) i) ∧
      (∀ i : Fin 3, sourcePointFunctional (SourceStatementPoints.points z i)
        (indexedMask half a b c (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j)) =
        sourcePointFunctional (SourceStatementPoints.points z i) (indexedMask half a b c g0)) ∧
      ((∑ v ∈ TwoSwapSourceTable.inactive, indexedMask half a b c
        (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j) v) =
        ∑ v ∈ TwoSwapSourceTable.inactive, indexedMask half a b c g0 v) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22, NormalizedQuerySection.evaluate
        (fun d => combination t ht noneOne alpha x (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 32, R370KernelEvaluation.firstFold 32 alpha (combination t ht noneOne alpha x) d = 0) := by
  let theta : F := (1-beta) / (scale*beta)
  let desired : Fin 7 → F := fun k => -theta * fullRelation half quarter a b c kappa tau z previous false r k.val -
    scale⁻¹ * fullRelation half quarter a b c kappa tau z previous true r k.val -
    fullRelation half quarter a b c kappa tau z previous false g0 k.val
  let desiredG : Fin 7 → F := fun k => -fullRelation half quarter a b c kappa tau z previous true g0 k.val
  have eval_add (u v w : Fin 7 → F) (A B : F) :
      evalSeven (fun k => A*u k+B*v k+w k) alpha =
        A*evalSeven u alpha+B*evalSeven v alpha+evalSeven w alpha := by
    simp only [evalSeven, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hd : evalSeven desired alpha = 0 := by
    have hrR := full_relation_eval_zero half quarter a b c kappa tau alpha z previous false r hf
    have hrG := full_relation_eval_zero half quarter a b c kappa tau alpha z previous true r hf
    have hgR := full_relation_eval_zero half quarter a b c kappa tau alpha z previous false g0 hfg
    have e := eval_add (fun k : Fin 7 => fullRelation half quarter a b c kappa tau z previous false r k.val)
      (fun k : Fin 7 => fullRelation half quarter a b c kappa tau z previous true r k.val)
      (fun k : Fin 7 => -fullRelation half quarter a b c kappa tau z previous false g0 k.val) (-theta) (-scale⁻¹)
    calc
      evalSeven desired alpha = evalSeven (fun k => -theta * fullRelation half quarter a b c kappa tau z previous false r k.val +
          (-scale⁻¹) * fullRelation half quarter a b c kappa tau z previous true r k.val +
          -fullRelation half quarter a b c kappa tau z previous false g0 k.val) alpha := by
            congr 1; funext k; dsimp [desired]; ring
      _ = -theta*evalSeven (fun k : Fin 7 => fullRelation half quarter a b c kappa tau z previous false r k.val) alpha +
          (-scale⁻¹)*evalSeven (fun k : Fin 7 => fullRelation half quarter a b c kappa tau z previous true r k.val) alpha +
          evalSeven (fun k : Fin 7 => -fullRelation half quarter a b c kappa tau z previous false g0 k.val) alpha := e
      _ = 0 := by
        have hneg : evalSeven (fun k : Fin 7 => -fullRelation half quarter a b c kappa tau z previous false g0 k.val) alpha = 0 := by
          simpa only [evalSeven, neg_mul, Finset.sum_neg_distrib, neg_zero] using congrArg Neg.neg hgR
        rw [hrR,hrG,hneg]
        ring
  have hdG : evalSeven desiredG alpha = 0 := by
    have h := full_relation_eval_zero half quarter a b c kappa tau alpha z previous true g0 hfg
    calc
      evalSeven desiredG alpha = - evalSeven (fun k : Fin 7 => fullRelation half quarter a b c kappa tau z previous true g0 k.val) alpha := by
        simp [evalSeven, desiredG, Finset.sum_neg_distrib]
      _ = 0 := by rw [h, neg_zero]
  have hbG : desiredG 0 + desiredG 4 = 0 := by
    have h := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter g0
      (fullWeight half a b c kappa tau z previous true)
    change fullRelation half quarter a b c kappa tau z previous true g0 0 + fullRelation half quarter a b c kappa tau z previous true g0 4 = _ at h
    rw [hgm, mul_zero] at h
    dsimp [desiredG]
    rw [← neg_add, h]
    simp
  have hb : desired 0 + desired 4 = 0 := by
    have hR := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter r
      (fullWeight half a b c kappa tau z previous false)
    have hRG := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter r
      (fullWeight half a b c kappa tau z previous true)
    have hG := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter g0
      (fullWeight half a b c kappa tau z previous false)
    change fullRelation half quarter a b c kappa tau z previous false r 0 + fullRelation half quarter a b c kappa tau z previous false r 4 = _ at hR
    change fullRelation half quarter a b c kappa tau z previous true r 0 + fullRelation half quarter a b c kappa tau z previous true r 4 = _ at hRG
    change fullRelation half quarter a b c kappa tau z previous false g0 0 + fullRelation half quarter a b c kappa tau z previous false g0 4 = _ at hG
    have hm : (fullRelation half quarter a b c kappa tau z previous true r 0 +
        fullRelation half quarter a b c kappa tau z previous true r 4) + scale *
        (fullRelation half quarter a b c kappa tau z previous false g0 0 +
        fullRelation half quarter a b c kappa tau z previous false g0 4) = 0 := by
      rw [hRG, hG]
      have hq : quarter * ((∑ d : Fin 256, ∑ s : Fin 4, r (d,s) * fullWeight half a b c kappa tau z previous true (d,s)) +
          scale * (∑ d : Fin 256, ∑ s : Fin 4, g0 (d,s) * fullWeight half a b c kappa tau z previous false (d,s))) = 0 := by
        rw [hcrossm, mul_zero]
      convert hq using 1 <;> ring
    have hinv : scale * scale⁻¹ = 1 := mul_inv_cancel₀ hscale
    have hR0 := hR
    rw [hrm, mul_zero] at hR0
    have hrz : fullRelation half quarter a b c kappa tau z previous false r 0 +
      fullRelation half quarter a b c kappa tau z previous false r 4 = 0 := hR0
    have hcancel : scale⁻¹ * (fullRelation half quarter a b c kappa tau z previous true r 0 +
      fullRelation half quarter a b c kappa tau z previous true r 4) +
      (fullRelation half quarter a b c kappa tau z previous false g0 0 +
      fullRelation half quarter a b c kappa tau z previous false g0 4) = 0 := by
      apply (mul_left_cancel₀ hscale)
      calc
        scale * (scale⁻¹ * (fullRelation half quarter a b c kappa tau z previous true r 0 +
          fullRelation half quarter a b c kappa tau z previous true r 4) +
          (fullRelation half quarter a b c kappa tau z previous false g0 0 +
          fullRelation half quarter a b c kappa tau z previous false g0 4)) =
          (fullRelation half quarter a b c kappa tau z previous true r 0 +
          fullRelation half quarter a b c kappa tau z previous true r 4) + scale *
          (fullRelation half quarter a b c kappa tau z previous false g0 0 +
          fullRelation half quarter a b c kappa tau z previous false g0 4) := by
            rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hscale]
            ring
        _ = 0 := by rw [hm]; simp
    calc
      desired 0 + desired 4 = -theta * (fullRelation half quarter a b c kappa tau z previous false r 0 + fullRelation half quarter a b c kappa tau z previous false r 4) -
          (scale⁻¹ * (fullRelation half quarter a b c kappa tau z previous true r 0 + fullRelation half quarter a b c kappa tau z previous true r 4) +
          (fullRelation half quarter a b c kappa tau z previous false g0 0 + fullRelation half quarter a b c kappa tau z previous false g0 4)) := by dsimp [desired]; ring
      _ = 0 := by rw [hrz, hcancel]; ring
  obtain ⟨x,hO,hG,hpoints,hcoins,hqueries,hfold,hbalance⟩ :=
    all_point_residual_pair_repair t ht noneOne half quarter a b c kappa alpha tau z previous desired desiredG hquarter hkappa hd hdG hb hbG hdet
  sorry

#print axioms fixed_beta_weak_moment_repair
end
end AspisV8R19.R672FixedBetaWeakMomentRepair
