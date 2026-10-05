import AspisV8R19.R884SelectedNormalizedSemanticPolynomial
import AspisV8R19.AdmissibleGridBound

/-! A finite product-grid count for the selected normalized semantic determinant.
It does not assert an adaptive source, oracle, or callback distribution. -/
set_option autoImplicit false
namespace AspisV8R19.R885CompleteSemanticGridBound
open MvPolynomial
open AspisV8R15.ExactTowerBase
open AspisV8R19.R791QM31JointNormalization
open AspisV8R19.R884SelectedNormalizedSemanticPolynomial
open scoped BigOperators
noncomputable section

local instance : Fact (1 < 2147483647) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2147483647) := m31PrimeFact
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

/-- For each fixed legal 22-root tuple, the singular fraction on any finite
15-coordinate product grid is bounded by the total degree over its minimum
coordinate-set size. -/
theorem selected_root_grid_bound (t : Fin 22 → QM31Exact)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (S : Fin 15 → Finset QM31Exact) (m : Nat) (hm : 0 < m)
    (hS : ∀ i, m ≤ (S i).card) :
    ((Fintype.piFinset S).filter (fun x => eval x
      (selectedRootPoly t ht noneOne).det = 0)).card /
      (∏ i, ((S i).card : ℚ≥0)) ≤ (14049 : ℚ≥0) / m := by
  classical
  exact AspisR19.AdmissibleGridBound.mixed_grid _
    (selectedRootPoly_det_ne_zero t ht noneOne)
    S m 14049 hm hS
    (selectedRootPoly_det_degree t ht noneOne)

#print axioms selected_root_grid_bound
end
end AspisV8R19.R885CompleteSemanticGridBound
