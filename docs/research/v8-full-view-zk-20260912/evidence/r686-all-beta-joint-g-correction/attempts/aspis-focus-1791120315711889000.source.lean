import AspisV8R19.R685FullJointGImage
import AspisV8R19.R675FullCorrectionMoments
import AspisV8R19.R662FullIndexedMaskPreservation
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R686AllBetaJointGCorrection
open AspisR19 AspisV8R16 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open R574SparseGCorePolynomial R645TwoSwapHighDirections R660FullSourceResidualCorrection
open R662FullIndexedMaskPreservation
open R675FullCorrectionMoments R681FullCoreCoinImage R682FullQueryNormalization
open R683QueryCoreCoinImage R685FullJointGImage
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]

theorem all_beta_joint_g_correction (half quarter a b c kappa alpha tau scale : F)
    (z : Fin 10 → F) (previous : Fin 271 → F)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (hquarter : quarter ≠ 0) (hkappa : kappa ≠ 0) (hscale : scale ≠ 0)
    (hcore : (coreMatrix half alpha a b c).det ≠ 0)
    (hresidual : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z previous t ht noneOne).det ≠ 0)
    (r : Index 256 → F)
    (hfoldr : ∀ d, R370KernelEvaluation.firstFold 256 alpha r d = 0)
    (hplainr : ∀ k : Fin 7, fullRelation half quarter a b c kappa tau z previous false r k.val = 0)
    (hstructuredmoment : ∑ d : Fin 256, ∑ s : Fin 4,
      r (d,s)*fullWeight half a b c kappa tau z previous true (d,s) = 0)
    (coinsTarget : Fin 271 → F)
    (hcoinmoment : ∑ i : Fin 271, SourceGConstant.finishCoins half previous i*coinsTarget i = 0) :
    ∃ g : Index 256 → F,
      (∀ i : Fin 271, actualCoin (indexedMask half a b c g) i = coinsTarget i) ∧
      (∀ i : Fin 3, sourcePointFunctional (SourceStatementPoints.points z i) (indexedMask half a b c g) = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22, evaluate256 (fun d => g (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 256, R370KernelEvaluation.firstFold 256 alpha g d = 0) ∧
      ((∑ u ∈ TwoSwapSourceTable.inactive, indexedMask half a b c g u) = 0) ∧
      (∀ beta : F, ∀ k : Fin 7, coefficient (sourceKernel 256 k.val quarter)
        (fun i => (1-beta)*r i+scale*beta*g i)
        (fun i => (1-beta)*fullWeight half a b c kappa tau z previous false i+
          beta*fullWeight half a b c kappa tau z previous true i)=0) ∧
      (scale * (rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true) (flattenFull g) -
        rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false) (flattenFull g)) -
        (rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true) (flattenFull r) -
        rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false) (flattenFull r)) = 0) := by
  have hrelrR := full_relation_eval_zero half quarter a b c kappa tau alpha z previous false r hfoldr
  have hrelrG := full_relation_eval_zero half quarter a b c kappa tau alpha z previous true r hfoldr
  have hboundaryrG : fullRelation half quarter a b c kappa tau z previous true r 0 +
      fullRelation half quarter a b c kappa tau z previous true r 4 = 0 := by
    unfold fullRelation
    rw [R653SourceCoefficientBoundary.coefficient_boundary,hstructuredmoment]
    ring
  let ordinaryTarget : Fin 7 → F := fun k => -scale⁻¹*
    fullRelation half quarter a b c kappa tau z previous true r k.val
  let structuredTarget : Fin 7 → F := fun _ => 0
  have hevalO : R652ResidualCoefficientCompletion.evalSeven ordinaryTarget alpha = 0 := by
    calc
      R652ResidualCoefficientCompletion.evalSeven ordinaryTarget alpha = -scale⁻¹*
        R652ResidualCoefficientCompletion.evalSeven (fun k : Fin 7 =>
          fullRelation half quarter a b c kappa tau z previous true r k.val) alpha := by
          unfold R652ResidualCoefficientCompletion.evalSeven ordinaryTarget
          simp only [neg_mul,Finset.sum_neg_distrib,mul_assoc]
          rw [← Finset.mul_sum]
      _ = 0 := by rw [hrelrG,mul_zero]
  have hevalG : R652ResidualCoefficientCompletion.evalSeven structuredTarget alpha = 0 := by
    simp [structuredTarget,R652ResidualCoefficientCompletion.evalSeven]
  have hboundaryO : ordinaryTarget 0+ordinaryTarget 4 = quarter*(kappa*(0:F)+kappa^2*0+kappa^3*0) := by
    unfold ordinaryTarget
    change -scale⁻¹*fullRelation half quarter a b c kappa tau z previous true r 0 +
      -scale⁻¹*fullRelation half quarter a b c kappa tau z previous true r 4 = _
    linear_combination (-scale⁻¹)*hboundaryrG
  have hboundaryG : structuredTarget 0+structuredTarget 4 =
      quarter*(kappa*(∑ i : Fin 271, SourceGConstant.finishCoins half previous i*coinsTarget i)+kappa^2*0+kappa^3*0) := by
    simp only [structuredTarget,hcoinmoment,mul_zero,add_zero]
  obtain ⟨g,hcoins,hpoints,hgR,hgG,hquery,hfoldg,hbalance⟩ :=
    full_joint_g_image half quarter a b c kappa alpha tau z previous t ht noneOne hquarter hkappa hcore hresidual
      coinsTarget (fun _ => 0) ordinaryTarget structuredTarget hevalO hevalG hboundaryO hboundaryG
  have hquad : ∀ beta : F, ∀ k : Fin 7, coefficient (sourceKernel 256 k.val quarter)
      (fun i => (1-beta)*r i+scale*beta*g i)
      (fun i => (1-beta)*fullWeight half a b c kappa tau z previous false i+
        beta*fullWeight half a b c kappa tau z previous true i)=0 := by
    intro beta k
    apply folded_coefficient_zero
    · exact hplainr k
    · change fullRelation half quarter a b c kappa tau z previous true r k.val +
        scale*fullRelation half quarter a b c kappa tau z previous false g k.val = 0
      rw [hgR]
      unfold ordinaryTarget
      field_simp [hscale]
      ring
    · exact hgG k
  have hplainrmoment : ∑ d : Fin 256, ∑ s : Fin 4,
      r (d,s)*fullWeight half a b c kappa tau z previous false (d,s) = 0 := by
    have h := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter r
      (fullWeight half a b c kappa tau z previous false)
    have h0 : fullRelation half quarter a b c kappa tau z previous false r 0 = 0 := by simpa using hplainr (0:Fin 7)
    have h4 : fullRelation half quarter a b c kappa tau z previous false r 4 = 0 := by simpa using hplainr (4:Fin 7)
    change fullRelation half quarter a b c kappa tau z previous false r 0 +
      fullRelation half quarter a b c kappa tau z previous false r 4 = _ at h
    rw [h0,h4,zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hquarter
  have hplainGmoment : ∑ d : Fin 256, ∑ s : Fin 4,
      g (d,s)*fullWeight half a b c kappa tau z previous false (d,s) = 0 := by
    have h := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter g
      (fullWeight half a b c kappa tau z previous false)
    have h0 : fullRelation half quarter a b c kappa tau z previous false g 0 = ordinaryTarget 0 := by simpa using hgR (0:Fin 7)
    have h4 : fullRelation half quarter a b c kappa tau z previous false g 4 = ordinaryTarget 4 := by simpa using hgR (4:Fin 7)
    change fullRelation half quarter a b c kappa tau z previous false g 0 +
      fullRelation half quarter a b c kappa tau z previous false g 4 = _ at h
    have hz : quarter*(∑ d : Fin 256, ∑ s : Fin 4,
        g (d,s)*fullWeight half a b c kappa tau z previous false (d,s))=0 := by
      rw [← h,h0,h4]
      unfold ordinaryTarget
      change -(scale⁻¹*fullRelation half quarter a b c kappa tau z previous true r 0) +
        -(scale⁻¹*fullRelation half quarter a b c kappa tau z previous true r 4) = 0
      linear_combination (-scale⁻¹)*hboundaryrG
    exact (mul_eq_zero.mp hz).resolve_left hquarter
  have hstructuredGmoment : ∑ d : Fin 256, ∑ s : Fin 4,
      g (d,s)*fullWeight half a b c kappa tau z previous true (d,s) = 0 := by
    have h := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter g
      (fullWeight half a b c kappa tau z previous true)
    have h0 : fullRelation half quarter a b c kappa tau z previous true g 0 = structuredTarget 0 := by simpa using hgG (0:Fin 7)
    have h4 : fullRelation half quarter a b c kappa tau z previous true g 4 = structuredTarget 4 := by simpa using hgG (4:Fin 7)
    change fullRelation half quarter a b c kappa tau z previous true g 0 +
      fullRelation half quarter a b c kappa tau z previous true g 4 = _ at h
    have hz : quarter*(∑ d : Fin 256, ∑ s : Fin 4,
        g (d,s)*fullWeight half a b c kappa tau z previous true (d,s))=0 := by
      rw [← h,h0,h4]
      simp [structuredTarget]
    exact (mul_eq_zero.mp hz).resolve_left hquarter
  have hcross : (∑ d : Fin 256, ∑ s : Fin 4,
      r (d,s)*fullWeight half a b c kappa tau z previous true (d,s)) + scale*
      (∑ d : Fin 256, ∑ s : Fin 4,
      g (d,s)*fullWeight half a b c kappa tau z previous false (d,s))=0 := by
    rw [hstructuredmoment,hplainGmoment]
    ring
  refine ⟨g,hcoins,hpoints,hquery,hfoldg,hbalance,hquad,?_⟩
  exact p2_of_moments half a b c kappa tau scale z previous r g hplainrmoment hstructuredGmoment hcross
#print axioms all_beta_joint_g_correction
end
end AspisV8R19.R686AllBetaJointGCorrection
