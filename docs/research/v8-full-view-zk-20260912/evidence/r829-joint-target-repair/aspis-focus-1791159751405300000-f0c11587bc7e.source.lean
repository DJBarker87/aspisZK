import AspisV8R19.R827JointCombinationKernel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
namespace AspisV8R19.R829JointTargetRepair
open AspisV8R19.R826JointCombinationObservation
open AspisV8R19.R827JointCombinationKernel
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R682FullQueryNormalization
open AspisR19.R370KernelEvaluation
open AspisR19.AugmentedQuerySection
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem joint_target_repair (half quarter alpha u v kappa tau : F)
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
        evaluate256 (fun d => combination alpha t ht noneOne x (d,slot)) (roots t root) = 0) := by
  let A := normalizedSelectedMatrix half quarter alpha u v kappa tau z t ht noneOne
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨x,hx⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) target
  refine ⟨x, ?_, combination_firstFold alpha t ht noneOne x,
    combination_query_root alpha t ht noneOne x, combination_augmented_root alpha t ht noneOne x⟩
  intro row
  rw [combination_observation]
  exact congrFun hx row

#print axioms joint_target_repair
end
end AspisV8R19.R829JointTargetRepair
