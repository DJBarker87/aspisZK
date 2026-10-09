import ResidualRecoveryCompositionV8
import SelectedResidualHighRecovery

/-! Source-review draft. Discharge the high-residual premise using the
SAME fixed family/classification and actual high witness. The final remains
adaptive and the suffix and Gamma/G/G/A means are unchanged. Prefix
existence and source/Fiat--Shamir coupling are not asserted here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedResidualRecoveryBound
open Polynomial Finset
open AspisV8.CausalCoveredRecovery AspisV8.SelectedHigherYHighSupport
open AspisV8.SelectedMiddleImageRecovery AspisV8.ComponentOODBinding
open AspisV8.SelectedRegularLayerCakeInstance
open AspisV8.SelectedResidualHighRecovery
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev Tuple := Fin 29 → Fin 1024 → K
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- Only the named mean wrappers differ. No recurrence, candidate, final,
or query schedule is evaluated or replaced by this definitional identity. -/
theorem high_probability_eq {q : Nat} (e : Execution q) (family : Finset Tuple)
    (A G Gamma : Finset K) :
    ResidualRecoveryComposition.highResidualProbability e
      (RecoveredHigh e family) A G Gamma =
      SelectedResidualHighRecovery.highResidualProbability e family A G Gamma := rfl

/-- The exact disjoint high-unrecovered/LOW partition for this particular
SAME-Q recovered event, carrying one and the same compact suffix. -/
theorem residual_partition {q : Nat} (e : Execution q) (family : Finset Tuple)
    (A G Gamma : Finset K) :
    ResidualRecoveryComposition.residualProbability e
      (RecoveredHigh e family) A G Gamma =
      SelectedResidualHighRecovery.highResidualProbability e family A G Gamma +
        SelectedRegularLowProbability.lowProbability e A G Gamma := by
  have partition := ResidualRecoveryComposition.probability_partition e
    (RecoveredHigh e family) (recovered_high_implies_high e family) A G Gamma
  rw [high_probability_eq] at partition
  exact partition

/-- Selected non-pair residual bound. The classifier and exact bad set
are fixed before gamma and work uniformly over all later histories. The
104/Gamma premise is derived, not supplied or treated as source acceptance. -/
theorem conditional_nonpair_bound {q : Nat} (e : Execution q)
    (Gamma : Finset K) (family : Finset Tuple) (one : family.card ≤ 1)
    (E beta : K[X]) (betaNonzero : beta ≠ 0) (betaDegree : beta.natDegree ≤ 40)
    (sparseSource : Finset K) (sparseSmall : sparseSource.card ≤ 28)
    (bad : Finset K)
    (sameBad : bad = SelectedMiddleImageRecovery.Generic.exceptionSet family
      (Gamma.filter fun gamma => beta.eval gamma=0) (sparseSource ∩ Gamma)
      (insufficientHits e.c1 e.c2 Gamma))
    (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1)
    (cover : CandidateClassifies e.c1 e.c2 Gamma family E beta sparseSource e.data)
    (outside : ¬∀ r, (E * SelectedSingularOODFamily.obstruction e.c1 e.c2).eval
      (SelectedOODGate.point e.data r) = 0)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (largeGamma : 6752623450 ≤ Gamma.card) (positive : 0 < q) (count : q ≤ 262144) :
    ResidualRecoveryComposition.residualProbability e
      (RecoveredHigh e family) A G Gamma ≤ (117153 : ℚ)/Gamma.card +
      integratedBudget q Gamma A + (q : ℚ)/G.card + 18/A.card := by
  have middleOutside := (ResidualRecoveryComposition.Generic.product_outside_generic E
    (SelectedSingularOODFamily.obstruction e.c1 e.c2)
    (SelectedOODGate.point e.data) outside).1
  have outsidePair : ¬PairRoot E e.data := middleOutside
  have selectedBound := SelectedResidualHighRecovery.high_residual_probability_bound e
    Gamma family one E beta betaNonzero betaDegree sparseSource sparseSmall bad sameBad
    checked circles west cover outsidePair A G ha hg count
  have highBound : ResidualRecoveryComposition.highResidualProbability e
      (RecoveredHigh e family) A G Gamma ≤ (104 : ℚ)/Gamma.card := by
    rw [high_probability_eq]
    exact selectedBound
  exact ResidualRecoveryComposition.conditional_nonpair_bound e checked circles west
    A G Gamma ha hg hgamma largeGamma positive count E outside
    (RecoveredHigh e family) (recovered_high_implies_high e family) highBound

#print axioms high_probability_eq
#print axioms residual_partition
#print axioms conditional_nonpair_bound
end
end AspisV8.SelectedResidualRecoveryBound
