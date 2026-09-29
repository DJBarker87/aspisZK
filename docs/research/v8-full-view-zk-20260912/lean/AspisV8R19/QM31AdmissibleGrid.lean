/- The actual source distribution is not equated with this finite uniform experiment. -/
import AspisV8R19.QM31ResidualBoundary
import AspisV8R19.AdmissibleGridBound

namespace AspisR19.QM31AdmissibleGrid
open AspisV8R15.ExactTowerBase SourceResidualPolynomial Finset Fintype
noncomputable section
local instance : DecidableEq QM31Exact := Classical.decEq _

def determinant := (polyMinor ((2 : QM31Exact)⁻¹) ((4 : QM31Exact)⁻¹)).det

theorem mixed_grid (S : Fin 36 → Finset QM31Exact) (m : Nat) (hm : 0 < m)
    (hS : ∀ i, m ≤ (S i).card) :
    ((piFinset S).filter (fun x => MvPolynomial.eval x determinant = 0)).card /
      (∏ i, ((S i).card : ℚ≥0)) ≤ (1105 : ℚ≥0) / m :=
  AdmissibleGridBound.mixed_grid determinant QM31ResidualBoundary.nonzero_and_degree.1
    S m 1105 hm hS QM31ResidualBoundary.nonzero_and_degree.2

theorem admitted_grid (S : Fin 36 → Finset QM31Exact)
    (admitted : Finset (Fin 36 → QM31Exact))
    (hsub : admitted ⊆ piFinset S) (hadm : admitted.Nonempty)
    (m : Nat) (hm : 0 < m) (hS : ∀ i, m ≤ (S i).card) :
    ((admitted.filter (fun x => MvPolynomial.eval x determinant = 0)).card : ℚ≥0) /
      admitted.card ≤
      ((1105 : ℚ≥0) / m) / ((admitted.card : ℚ≥0) / (piFinset S).card) :=
  AdmissibleGridBound.admitted_grid determinant QM31ResidualBoundary.nonzero_and_degree.1
    S admitted hsub hadm m 1105 hm hS QM31ResidualBoundary.nonzero_and_degree.2

theorem nonzero_implies_selected_surjective (x : Fin 36 → QM31Exact)
    (h : MvPolynomial.eval x determinant ≠ 0) :
    Function.Surjective (assignedMinor ((2:QM31Exact)⁻¹) ((4:QM31Exact)⁻¹) x).mulVec :=
  QM31ResidualBoundary.selected_residual_surjective x h

#print axioms mixed_grid
#print axioms admitted_grid
#print axioms nonzero_implies_selected_surjective
end
end AspisR19.QM31AdmissibleGrid
