import AspisV8R19.R832BalancedJointTargetRepair
import AspisV8R19.R852FullOrdinaryCoefficientBoundary
import AspisV8R19.R370KernelEvaluation

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R855JointDeterminantFourthRoot

open AspisV8R19.R826JointCombinationObservation
open AspisV8R19.R832BalancedJointTargetRepair
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R852FullOrdinaryCoefficientBoundary
open AspisR19.R370KernelEvaluation
open AspisV8R17 AspisR19
open scoped BigOperators

noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem determinant_excludes_fourth_root
    (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (hdet : (normalizedSelectedMatrix half quarter alpha u v kappa tau z t ht noneOne).det ≠ 0) :
    alpha^4 ≠ 1 := by
  intro ha4
  let target : R738JointObservationModel.ObservationRow → F
    | .inl _ => 0
    | .inr (.inl _) => 0
    | .inr (.inr j) => if j.val = 0 then 1 else 0
  obtain ⟨x,hobs,hfold,hquery,haug,hTop,hbalance⟩ :=
    balanced_joint_target_repair half quarter alpha u v kappa tau z t ht noneOne target hdet
  let q : Index256 → F := R826JointCombinationObservation.combination alpha t ht noneOne x
  have hpoint0 : sourcePointFunctional (SourceStatementPoints.points z 0)
      (rawMask half (1+u*v) (u*v-1) (-(u+v)) q) = 0 := by
    have h := hobs (.inr (.inl (0 : Fin 3)))
    simpa [q, target, rawObservation] using h
  have hpoint1 : sourcePointFunctional (SourceStatementPoints.points z 1)
      (rawMask half (1+u*v) (u*v-1) (-(u+v)) q) = 0 := by
    have h := hobs (.inr (.inl (1 : Fin 3)))
    simpa [q, target, rawObservation] using h
  have hpoint2 : sourcePointFunctional (SourceStatementPoints.points z 2)
      (rawMask half (1+u*v) (u*v-1) (-(u+v)) q) = 0 := by
    have h := hobs (.inr (.inl (2 : Fin 3)))
    simpa [q, target, rawObservation] using h
  have hrel1 : rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
      kappa tau z q 1 = 1 := by
    have h := hobs (.inr (.inr (0 : Fin 5)))
    simpa [q, target, rawObservation, relationIndex] using h
  have hrel2 : rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
      kappa tau z q 2 = 0 := by
    have h := hobs (.inr (.inr (1 : Fin 5)))
    simpa [q, target, rawObservation, relationIndex] using h
  have hrel3 : rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
      kappa tau z q 3 = 0 := by
    have h := hobs (.inr (.inr (2 : Fin 5)))
    simpa [q, target, rawObservation, relationIndex] using h
  have hrel5 : rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
      kappa tau z q 5 = 0 := by
    have h := hobs (.inr (.inr (3 : Fin 5)))
    simpa [q, target, rawObservation, relationIndex] using h
  have hrel6 : rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
      kappa tau z q 6 = 0 := by
    have h := hobs (.inr (.inr (4 : Fin 5)))
    simpa [q, target, rawObservation, relationIndex] using h
  have htopRaw : ∀ r : Nat, 1020 ≤ r → rawFlatten q r = 0 := by
    intro r hr
    rw [rawFlatten_eq_flattenFull]
    exact hTop r hr
  have hboundary :
      rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q 0 +
      rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q 4 = 0 := by
    rw [ordinary_coefficient_boundary_of_top_zero
      half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q htopRaw]
    simp only [hpoint0, hpoint1, hpoint2, mul_zero, zero_add]
  let w : Fin 256 × Fin 4 → F := fun i =>
    rawOrdinaryWeight half (1+u*v) (u*v-1) (-(u+v)) kappa tau z
      (4*i.1.val+i.2.val)
  have hkernel : kernelEval 256 quarter alpha q w = 0 := by
    apply kernel_eval_zero_of_first_fold 256 quarter alpha q w
    intro d
    exact hfold d
  have hsum :
      (∑ k : Fin 7,
        rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q k.val * alpha^k.val) = 0 := by
    change (∑ k : Fin 7,
      rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q k.val * alpha^k.val) = 0 at hkernel
    exact hkernel
  have hpoly :
      rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q 0 +
        alpha + alpha^4 *
          rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q 4 = 0 := by
    simpa [Fin.sum_univ_succ, hrel1, hrel2, hrel3, hrel5, hrel6] using hsum
  rw [ha4] at hpoly
  have halpha : alpha = 0 := by
    linear_combination hpoly - hboundary
  rw [halpha] at ha4
  norm_num at ha4

#print axioms determinant_excludes_fourth_root

end
end AspisV8R19.R855JointDeterminantFourthRoot
