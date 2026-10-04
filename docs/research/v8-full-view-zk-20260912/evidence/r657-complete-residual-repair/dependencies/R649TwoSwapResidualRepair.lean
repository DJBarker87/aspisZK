import AspisV8R19.R648AugmentedTwoSwapKernel
import AspisV8R19.TwoSwapResidualSource
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R649TwoSwapResidualRepair
open AspisR19 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

private theorem weighted_dot {I J : Type*} [Fintype I] [Fintype J]
    (x : J → F) (q : J → I → F) (w : I → F) :
    (∑ i, (∑ j, x j * q j i) * w i) =
      ∑ j, x j * (∑ i, q j i * w i) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

private theorem coefficient_as_dot {I J : Type*} [Fintype I] [Fintype J]
    (C : I → J → F) (q : I → F) (w : J → F) :
    coefficient C q w = ∑ i, q i * (∑ j, C i j * w j) := by
  unfold coefficient
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem observed_combination (half quarter a b c kappa : F)
    (z : Fin 10 → F) (x : Fin 13 → F) (qs : Fin 13 → Index 32 → F) (row : Nat) :
    TwoSwapResidualModel.observed half quarter a b c kappa z
      (fun i => ∑ j, x j * qs j i) row =
      ∑ j, x j * TwoSwapResidualModel.observed half quarter a b c kappa z (qs j) row := by
  unfold TwoSwapResidualModel.observed
  split_ifs
  · exact weighted_dot x qs _
  · simp_rw [coefficient_as_dot]
    exact weighted_dot x qs _
  · simp_rw [coefficient_as_dot]
    exact weighted_dot x qs _

def combination (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (alpha : F) (x : Fin 13 → F) : Index 32 → F :=
  fun i => ∑ j, x j * AugmentedQuotient.quotient t ht noneOne alpha
    (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) i

/-- A nonzero exact source-shaped residual minor supplies every selected
13-coordinate target through a combination of its actual augmented columns.
Neither nonsingularity of a sampled prefix nor completeness of this selected
observation set is assumed proved here. -/
theorem selected_residual_repair (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half quarter a b c kappa alpha tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (target : Fin 13 → F)
    (hdet : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
      previous t ht noneOne).det ≠ 0) :
    ∃ x : Fin 13 → F, ∀ i : Fin 13,
      TwoSwapResidualSource.observed half quarter a b c kappa tau z previous
        (combination t ht noneOne alpha x) (ResidualModel.selectedRow i) = target i := by
  let M := TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
    previous t ht noneOne
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨x,hx⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) target
  refine ⟨x,?_⟩
  intro i
  rw [TwoSwapResidualSource.observed_eq]
  unfold combination
  rw [observed_combination]
  have hi := congrFun hx i
  change (∑ j, M i j * x j) = target i at hi
  rw [← hi]
  apply Finset.sum_congr rfl
  intro j _
  unfold M TwoSwapResidualSource.matrix
  rw [TwoSwapResidualSource.observed_eq]
  ring

#print axioms selected_residual_repair
#print axioms observed_combination
end
end AspisV8R19.R649TwoSwapResidualRepair
