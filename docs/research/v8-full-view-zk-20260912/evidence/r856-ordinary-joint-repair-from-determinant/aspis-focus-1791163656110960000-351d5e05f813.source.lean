import AspisV8R19.R854CompleteOrdinaryJointRepair
import AspisV8R19.R855JointDeterminantFourthRoot

set_option autoImplicit false
namespace AspisV8R19.R856OrdinaryJointRepairFromDeterminant
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R826JointCombinationObservation
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R652ResidualCoefficientCompletion
open AspisR19.R370KernelEvaluation
open AspisR19.AugmentedQuerySection
open AspisV8R19.R682FullQueryNormalization
open AspisV8R19.R662FullIndexedMaskPreservation
open scoped BigOperators
open AspisV8R19.R854CompleteOrdinaryJointRepair
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem complete_ordinary_joint_repair
    (half quarter alpha u v kappa tau : F) (z : Fin 10 → F)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (active : J → F) (points : Fin 3 → F) (desired : Fin 7 → F)
    (he : evalSeven desired alpha = 0)
    (hb : desired 0 + desired 4 =
      quarter * (kappa*points 0+kappa^2*points 1+kappa^3*points 2))
    (hdet : (normalizedSelectedMatrix half quarter alpha u v kappa tau z t ht noneOne).det ≠ 0) :
    ∃ x : R738JointObservationModel.ObservationRow → F,
      (∀ row, rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (combination alpha t ht noneOne x) row = jointTarget active points desired row) ∧
      (∀ k : Fin 7, rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (combination alpha t ht noneOne x) k.val = desired k) ∧
      (∀ d : Fin 256, firstFold 256 alpha (combination alpha t ht noneOne x) d = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22,
        evaluate256 (fun d => combination alpha t ht noneOne x (d,slot)) (t root) = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 23,
        evaluate256 (fun d => combination alpha t ht noneOne x (d,slot)) (roots t root) = 0) ∧
      (∀ r : Nat, 1020 ≤ r → flattenFull (combination alpha t ht noneOne x) r = 0) ∧
      (∑ r ∈ TwoSwapSourceTable.inactive,
        rawMask half (1+u*v) (u*v-1) (-(u+v)) (combination alpha t ht noneOne x) r) = 0 := by
  exact R854CompleteOrdinaryJointRepair.complete_ordinary_joint_repair
    half quarter alpha u v kappa tau z t ht noneOne active points desired
    (R855JointDeterminantFourthRoot.determinant_excludes_fourth_root
      half quarter alpha u v kappa tau z t ht noneOne hdet) he hb hdet

#print axioms complete_ordinary_joint_repair
end
end AspisV8R19.R856OrdinaryJointRepairFromDeterminant
