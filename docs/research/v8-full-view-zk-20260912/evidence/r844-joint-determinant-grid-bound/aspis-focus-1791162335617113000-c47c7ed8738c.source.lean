import AspisV8R19.R843CompleteJointDegree
import AspisV8R19.R835RootFixedJointPolynomialNonzero
import AspisV8R19.AdmissibleGridBound

/-! Exact finite product-domain bound for the actual-field polynomial.
This does not assert the actual adaptive source/oracle realizes a product law. -/
set_option autoImplicit false
namespace AspisV8R19.R844JointDeterminantGridBound
open MvPolynomial
open AspisV8R15.ExactTowerBase
open AspisV8R19.R779FixedPoint1LowKernel
open AspisV8R19.R791QM31JointNormalization
open AspisV8R19.R833RootFixedJointPolynomial
open scoped BigOperators
noncomputable section
local instance : Fact (1 < 2147483647) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2147483647) := m31PrimeFact
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

theorem fixed_root_grid_bound (t : Fin 22 → QM31Exact)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (S : Fin 15 → Finset QM31Exact) (m : Nat) (hm : 0 < m)
    (hS : ∀ i, m ≤ (S i).card) :
    ((Fintype.piFinset S).filter (fun x => eval x
      (rootFixedMatrix (witnessEmbedding half)
        (witnessEmbedding (536870912 : M)) t ht noneOne).det = 0)).card /
      (∏ i, ((S i).card : ℚ≥0)) ≤ (13986 : ℚ≥0) / m := by
  classical
  exact AspisR19.AdmissibleGridBound.mixed_grid _
    (R835RootFixedJointPolynomialNonzero.root_fixed_det_nonzero t ht noneOne)
    S m 13986 hm hS
    (R843CompleteJointDegree.normalized_det_degree _ _ t ht noneOne)

#print axioms fixed_root_grid_bound
end
end AspisV8R19.R844JointDeterminantGridBound
