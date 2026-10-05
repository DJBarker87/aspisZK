import AspisV8R19.R824SourceBlockTriangular
import AspisV8R19.R821AllSourceDiagonalUnits
import AspisV8R19.R809SourceBlockAssembly
import AspisV8R19.R794QM31JointDeterminantTransfer

set_option autoImplicit false
namespace AspisV8R19.R825CompleteSourceDeterminant
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry (z)
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R15.ExactTowerBase
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R791QM31JointNormalization
noncomputable section
local instance : Fact (1 < 2147483647) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2147483647) := m31PrimeFact
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

 theorem fixed_source_det_unit : IsUnit fixedSourceMatrix.det :=
  R809SourceBlockAssembly.fixedSourceMatrix_det_unit_of_blocks
    R824SourceBlockTriangular.source_block_triangular
    R821AllSourceDiagonalUnits.all_source_diagonal_units

 theorem fixed_source_det_ne_zero : fixedSourceMatrix.det ≠ 0 :=
  fixed_source_det_unit.ne_zero

 theorem chosen_source_det_ne_zero :
    (chosenSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z).det ≠ 0 := by
  have h := fixed_source_det_ne_zero
  unfold fixedSourceMatrix at h
  rw [literalSourceMatrix_det] at h
  exact h

 theorem selected_polynomial_det_ne_zero :
    (selectedPolynomialMatrix halfSelected quarterSelected).det ≠ 0 := by
  intro h
  have he := selected_matrix_det_eval halfSelected quarterSelected alphaSelected uSelected
    vSelected kappaSelected tauSelected z
  rw [h, map_zero] at he
  exact chosen_source_det_ne_zero he.symm

 theorem normalized_qm31_det_ne_zero (t : Fin 22 → QM31Exact)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    (normalizedSelectedMatrix (witnessEmbedding R779FixedPoint1LowKernel.half)
      (witnessEmbedding (536870912 : R779FixedPoint1LowKernel.M)) 7 2 3 5 0
      (fun i => witnessEmbedding (z i)) t ht noneOne).det ≠ 0 := by
  exact R794QM31JointDeterminantTransfer.normalized_qm31_det_ne_zero_of_source
    chosen_source_det_ne_zero t ht noneOne

#print axioms fixed_source_det_unit
#print axioms fixed_source_det_ne_zero
#print axioms chosen_source_det_ne_zero
#print axioms selected_polynomial_det_ne_zero
#print axioms normalized_qm31_det_ne_zero
end
end AspisV8R19.R825CompleteSourceDeterminant
