import AspisV8R19.R891Full223CompleteOrdinaryRepair
import AspisV8R19.R852FullOrdinaryCoefficientBoundary

set_option autoImplicit false
namespace AspisV8R19.R893SourceCompatible223Repair
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.R645TwoSwapHighDirections
open AspisR19.R370KernelEvaluation
open AspisR19.AugmentedQuerySection
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R887Full223CombinationObservation
open AspisV8R19.R682FullQueryNormalization
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R19.R852FullOrdinaryCoefficientBoundary
open AspisV8R19.R882RootFixedAugmentedPolynomial
open AspisV8R19.R891Full223CompleteOrdinaryRepair
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- A full223 nonsingular normalized matrix repairs any source-compatible
observation target induced by an input whose fold and four-coordinate top tail
are zero.  The input hypotheses remain explicit. -/
theorem source_compatible_223_repair
    (half quarter alpha u v kappa tau : F) (z : Fin 10 → F) (coins : RoundCoins F 10)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (r : R738JointObservationModel.Index256 → F) (hfold : ∀ d : Fin 256, firstFold 256 alpha r d = 0)
    (htop : ∀ n : Nat, 1020 ≤ n → flattenFull r n = 0) (semanticTarget : F)
    (hdet : (normalizedSource223 half quarter alpha u v kappa tau z coins t ht noneOne).det ≠ 0) :
    ∃ x : R887Full223CombinationObservation.Obs ⊕ Unit → F,
      (∀ row, rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (combination223 alpha t ht noneOne x) row =
        rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z r row) ∧
      ((∑ i : Fin 271, maskWeights271 half coins i * actualCoin
        (indexedMask half (1+u*v) (u*v-1) (-(u+v)) (combination223 alpha t ht noneOne x)) i) = semanticTarget) ∧
      (∀ k : Fin 7, rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (combination223 alpha t ht noneOne x) k.val =
        rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z r k.val) ∧
      (∀ d : Fin 256, firstFold 256 alpha (combination223 alpha t ht noneOne x) d = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22,
        evaluate256 (fun d => combination223 alpha t ht noneOne x (d,slot)) (t root) = 0) ∧
      (∀ slot : Fin 4, ∀ root : Fin 23,
        evaluate256 (fun d => combination223 alpha t ht noneOne x (d,slot)) (roots t root) = 0) ∧
      (∀ n : Nat, 1020 ≤ n → flattenFull (combination223 alpha t ht noneOne x) n = 0) ∧
      (∑ n ∈ TwoSwapSourceTable.inactive,
        rawMask half (1+u*v) (u*v-1) (-(u+v)) (combination223 alpha t ht noneOne x) n) = 0 := by
  let active : J → F := fun j => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v))
    kappa tau z r (.inl j)
  let points : Fin 3 → F := fun p => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v))
    kappa tau z r (.inr (.inl p))
  let desired : Fin 7 → F := fun k => rawRelation half quarter (1+u*v) (u*v-1) (-(u+v))
    kappa tau z r k.val
  have he : evalSeven desired alpha = 0 := by
    exact kernel_eval_zero_of_first_fold 256 quarter alpha r
      (fun i => rawOrdinaryWeight half (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (4*i.1.val+i.2.val)) hfold
  have htopRaw : ∀ n : Nat, 1020 ≤ n → rawFlatten r n = 0 := by
    intro n hn
    rw [rawFlatten_eq_flattenFull]
    exact htop n hn
  have hb : desired 0 + desired 4 =
      quarter * (kappa*points 0+kappa^2*points 1+kappa^3*points 2) := by
    change rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z r 0 +
      rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z r 4 = _
    rw [ordinary_coefficient_boundary_of_top_zero
      half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z r htopRaw]
    rfl
  obtain ⟨x,hobs,hsemantic,hrel,hfoldx,hquery,haug,htopx,hbalance⟩ :=
    complete_ordinary_joint_repair half quarter alpha u v kappa tau z coins t ht noneOne
      active points desired semanticTarget he hb hdet
  refine ⟨x, ?_, hsemantic, ?_, hfoldx,hquery,haug,htopx,hbalance⟩
  · intro row
    rw [hobs row]
    rcases row with j | p | k
    · rfl
    · rfl
    · exact hrel ⟨relationIndex k, by
        fin_cases k <;> decide⟩
  · intro k
    simpa [desired] using hrel k

#print axioms source_compatible_223_repair
end
end AspisV8R19.R893SourceCompatible223Repair
