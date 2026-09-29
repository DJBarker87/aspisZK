/- Algebraic endpoint only. The good-event probability is not a premise silently discharged. -/
import AspisV8R19.QM31ResidualWitness
import AspisV8R19.SourceResidualDegree
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace AspisR19.QM31ResidualBoundary
open AspisV8R15.ExactTowerBase SourceResidualPolynomial
noncomputable section

theorem nonzero_and_degree :
    (polyMinor ((2:QM31Exact)⁻¹) ((4:QM31Exact)⁻¹)).det ≠ 0 ∧
    (polyMinor ((2:QM31Exact)⁻¹) ((4:QM31Exact)⁻¹)).det.totalDegree ≤ 1105 :=
  ⟨QM31ResidualWitness.restricted_polynomial_ne_zero,
   SourceResidualDegree.determinant_degree _ _⟩

theorem selected_residual_surjective (s : Fin 36 → QM31Exact)
    (good : MvPolynomial.eval s (polyMinor ((2:QM31Exact)⁻¹) ((4:QM31Exact)⁻¹)).det ≠ 0) :
    Function.Surjective (assignedMinor ((2:QM31Exact)⁻¹) ((4:QM31Exact)⁻¹) s).mulVec := by
  apply Matrix.mulVec_surjective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [← determinant_evaluation]
  exact good

#print axioms nonzero_and_degree
#print axioms selected_residual_surjective
end
end AspisR19.QM31ResidualBoundary
