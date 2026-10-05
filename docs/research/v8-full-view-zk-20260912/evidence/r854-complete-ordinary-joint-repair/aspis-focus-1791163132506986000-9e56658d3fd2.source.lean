import AspisV8R19.R832BalancedJointTargetRepair
import AspisV8R19.R852FullOrdinaryCoefficientBoundary
import AspisV8R19.R853JointCoefficientCompletion

/-! Complete seven-coefficient ordinary target repair. Compatibility and
fourth-root degeneracy are explicit; legal-witness applicability remains open. -/
set_option autoImplicit false
namespace AspisV8R19.R854CompleteOrdinaryJointRepair
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
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

private theorem relationIndex_lt (k : Fin 5) : relationIndex k < 7 := by
  fin_cases k <;> decide

def jointTarget (active : J → F) (points : Fin 3 → F) (desired : Fin 7 → F) :
    R738JointObservationModel.ObservationRow → F
  | .inl j => active j
  | .inr (.inl p) => points p
  | .inr (.inr k) => desired ⟨relationIndex k, relationIndex_lt k⟩

theorem complete_ordinary_joint_repair
    (half quarter alpha u v kappa tau : F) (z : Fin 10 → F)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (active : J → F) (points : Fin 3 → F) (desired : Fin 7 → F)
    (ha : alpha^4 ≠ 1) (he : evalSeven desired alpha = 0)
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
  obtain ⟨x,hobs,hfold,hquery,haug,htop,hbalance⟩ :=
    R832BalancedJointTargetRepair.balanced_joint_target_repair
      half quarter alpha u v kappa tau z t ht noneOne
      (jointTarget active points desired) hdet
  let q := combination alpha t ht noneOne x
  let r : Fin 7 → F := fun k => rawRelation half quarter (1+u*v) (u*v-1)
    (-(u+v)) kappa tau z q k.val
  have hp (p : Fin 3) :
      sourcePointFunctional (SourceStatementPoints.points z p)
        (rawMask half (1+u*v) (u*v-1) (-(u+v)) q) = points p :=
    hobs (.inr (.inl p))
  have htq : ∀ n, 1020 ≤ n → rawFlatten q n = 0 := by
    intro n hn
    rw [rawFlatten_eq_flattenFull]
    exact htop n hn
  have hboundary : r 0 + r 4 = desired 0 + desired 4 := by
    rw [hb]
    change rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q 0 +
      rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q 4 = _
    rw [R852FullOrdinaryCoefficientBoundary.ordinary_coefficient_boundary_of_top_zero
      half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z q htq]
    rw [hp 0,hp 1,hp 2]
  have hre : evalSeven r alpha = 0 := by
    exact kernel_eval_zero_of_first_fold 256 quarter alpha q
      (fun i => rawOrdinaryWeight half (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (4*i.1.val+i.2.val)) hfold
  have hselected (k : Fin 5) : r ⟨relationIndex k, relationIndex_lt k⟩ =
      desired ⟨relationIndex k, relationIndex_lt k⟩ := hobs (.inr (.inr k))
  have hdiff : ∀ k, r k - desired k = 0 := by
    apply R853JointCoefficientCompletion.joint_completion _ alpha ha
    · simpa only [evalSeven,sub_mul,Finset.sum_sub_distrib,hre,he,sub_self]
    · linear_combination hboundary
    · intro k hk0 hk4
      fin_cases k
      · exact False.elim (hk0 rfl)
      · exact sub_eq_zero.mpr (hselected 0)
      · exact sub_eq_zero.mpr (hselected 1)
      · exact sub_eq_zero.mpr (hselected 2)
      · exact False.elim (hk4 rfl)
      · exact sub_eq_zero.mpr (hselected 3)
      · exact sub_eq_zero.mpr (hselected 4)
  exact ⟨x,hobs,(fun k => sub_eq_zero.mp (hdiff k)),hfold,hquery,haug,htop,hbalance⟩

#print axioms complete_ordinary_joint_repair
end
end AspisV8R19.R854CompleteOrdinaryJointRepair
