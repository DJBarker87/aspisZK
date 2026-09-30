import AspisV8R19.TwoSwapDomainProbability
import AspisV8R19.AdmissibleGridBound

/-! The fixed-root exceptional-set bound after imposing the distinctness
restriction on the two OOD coordinates.  The acceptance-ratio factor is kept
explicit; this file does not identify a source sampler with this restricted
product grid. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapDistinctRestriction
open MvPolynomial AspisV8R15.ExactTowerBase QM31ResidualWitness
open AspisR19.TwoSwapFixedRootProbability
open AspisR19.AdmissibleGridBound
noncomputable section

local instance cm31Fintype : Fintype CM31Exact :=
  Fintype.ofEquiv (M31Exact × M31Exact)
    (QuadraticAlgebra.equivProd (-1 : M31Exact) 0).symm

local instance qm31Fintype : Fintype QM31Exact :=
  Fintype.ofEquiv (CM31Exact × CM31Exact)
    (QuadraticAlgebra.equivProd qm31R 0).symm

def distinctAdmitted (S : Fin 36 → Finset QM31Exact) :
    Finset (Fin 36 → QM31Exact) :=
  (Fintype.piFinset S).filter
    (fun x => x (12 : Fin 36) ≠ x (13 : Fin 36))

theorem fixed_root_distinct_domains
    (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1)
    (S : Fin 36 → Finset QM31Exact) (m : Nat) (mpos : 0 < m)
    (domainSize : ∀ i, m ≤ (S i).card)
    (hadm : (distinctAdmitted S).Nonempty) :
    ((Finset.filter
        (fun s => eval s (determinantFor t ht noneOne) = 0)
        (distinctAdmitted S)).card : ℚ≥0) /
        (distinctAdmitted S).card ≤
      ((819 : ℚ≥0) / m) /
        (((distinctAdmitted S).card : ℚ≥0) /
          (Fintype.piFinset S).card) := by
  exact AspisR19.AdmissibleGridBound.admitted_grid
    (determinantFor t ht noneOne) (determinant_ne_zero t ht noneOne)
    S (distinctAdmitted S) (Finset.filter_subset _ _) hadm
    m 819 mpos domainSize (determinant_degree t ht noneOne)

#print axioms fixed_root_distinct_domains
end
end AspisR19.TwoSwapDistinctRestriction
