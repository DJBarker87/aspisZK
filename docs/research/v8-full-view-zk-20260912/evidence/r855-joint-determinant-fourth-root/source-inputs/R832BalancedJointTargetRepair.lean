import AspisV8R19.R829JointTargetRepair
import AspisV8R19.R831JointCombinationBalance

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R832BalancedJointTargetRepair
open AspisV8R19.R826JointCombinationObservation
open AspisV8R19.R829JointTargetRepair
open AspisV8R19.R831JointCombinationBalance
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R682FullQueryNormalization
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R16 AspisR19 AspisR19.R370KernelEvaluation AspisR19.AugmentedQuerySection
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem balanced_joint_target_repair (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (target : R738JointObservationModel.ObservationRow → F)
    (hdet : (normalizedSelectedMatrix half quarter alpha u v kappa tau z t ht noneOne).det ≠ 0) :
    ∃ x : R738JointObservationModel.ObservationRow → F,
      (∀ row, rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (combination alpha t ht noneOne x) row = target row) ∧
      (∀ d : Fin 256, firstFold 256 alpha (combination alpha t ht noneOne x) d = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22,
        evaluate256 (fun d => combination alpha t ht noneOne x (d,slot)) (t root) = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 23,
        evaluate256 (fun d => combination alpha t ht noneOne x (d,slot)) (roots t root) = 0) ∧
      (∀ r : Nat, 1020 ≤ r → flattenFull (combination alpha t ht noneOne x) r = 0) ∧
      (∑ r ∈ TwoSwapSourceTable.inactive,
        rawMask half (1+u*v) (u*v-1) (-(u+v)) (combination alpha t ht noneOne x) r) = 0 := by
  obtain ⟨x,hobs,hfold,hquery,haug⟩ :=
    joint_target_repair half quarter alpha u v kappa tau z t ht noneOne target hdet
  exact ⟨x,hobs,hfold,hquery,haug,flatten_combination_top alpha t ht noneOne x,
    rawMask_combination_balanced half (1+u*v) (u*v-1) (-(u+v)) alpha t ht noneOne x⟩

#print axioms balanced_joint_target_repair
end
end AspisV8R19.R832BalancedJointTargetRepair
