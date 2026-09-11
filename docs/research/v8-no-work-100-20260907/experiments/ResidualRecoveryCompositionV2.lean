import MiddleSimplePairMassV4
import SelectedHigherYProbability
import NestedCircleContinuationV2

/-! V2 source-review draft, not kernel-checked. V1 is retained unchanged. Product obstruction and one
conditional residual/LOW composition. The SAME middle E is supplied, never
reselected. Recovery and its high-residual bound remain explicit premises;
there is no acceptance, commitment-binding, or fresh-oracle assertion.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.ResidualRecoveryComposition
open Polynomial Finset
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

namespace Generic

/-- A product pair includes both original pair events and may also include
mixed roots. The converse is deliberately not asserted. -/
theorem pair_product {L : Type*} [Field L] (E F : L[X]) (points : Fin 2 → L)
    (hit : (∀ r, E.eval (points r) = 0) ∨ ∀ r, F.eval (points r) = 0) :
    ∀ r, (E*F).eval (points r) = 0 := by
  intro r
  rw [Polynomial.eval_mul]
  rcases hit with left | right
  · rw [left r, zero_mul]
  · rw [right r, mul_zero]

/-- Exact weighted partition, including the SAME suffix weight on both
branches. A recovered high prefix is removed, not bounded as a failure. -/
theorem gated_partition (higher high recovered : Prop)
    (highHigher : high → higher) (recoveredHigh : recovered → high) (weight : ℚ) :
    (if higher ∧ ¬recovered then weight else 0) =
      (if high ∧ ¬recovered then weight else 0) +
      (if higher ∧ ¬high then weight else 0) := by
  classical
  by_cases selected : high
  · have present := highHigher selected
    simp only [selected, present, true_and, not_true_eq_false, and_false,
      if_false, add_zero]
  · have notRecovered : ¬recovered := fun yes => selected (recoveredHigh yes)
    simp only [selected, notRecovered, not_false_eq_true, and_true, false_and,
      if_false, zero_add]
end Generic

open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.RootSetPairMass AspisV8.NestedCircleMass
open AspisV8.SecureCircleParameterDomain
open AspisV8.CausalCoveredRecovery AspisV8.CausalHigherYClassification
open AspisV8.SelectedHigherYBranch
open AspisV8.SelectedHigherYHighSupport AspisV8.SelectedRegularLowProbability
open AspisV8.SelectedRegularLayerCakeInstance
open AspisV8.JointImageGame AspisV8.RelationCompatibleMoment
open AspisV8.ComponentOODBinding
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

/-- E is exactly the caller's pre-OOD middle obstruction. -/
def productObstruction (c1 : C1Received) (c2 : C2Received) (E : K[X]) : K[X] :=
  E * SelectedSingularOODFamily.obstruction c1 c2

set_option maxRecDepth 400 in
theorem product_nonzero_degree (c1 : C1Received) (c2 : C2Received) (E : K[X])
    (nonzero : E ≠ 0) (degree : E.natDegree ≤ 65061549) :
    productObstruction c1 c2 E ≠ 0 ∧
      (productObstruction c1 c2 E).natDegree ≤ 90407376 := by
  have low := SelectedSingularOODFamily.fixed_cover c1 c2
  constructor
  · exact mul_ne_zero nonzero low.1
  · have sumBound : E.natDegree +
        (SelectedSingularOODFamily.obstruction c1 c2).natDegree ≤ 90407376 := by
      have lowDegree := low.2.1
      omega
    exact Polynomial.natDegree_mul_le.trans sumBound

set_option maxRecDepth 400 in
theorem product_outside (c1 : C1Received) (c2 : C2Received) (E : K[X])
    (points : Fin 2 → K)
    (outside : ¬∀ r, (productObstruction c1 c2 E).eval (points r) = 0) :
    (¬∀ r, E.eval (points r) = 0) ∧
      ¬∀ r, (SelectedSingularOODFamily.obstruction c1 c2).eval (points r) = 0 := by
  constructor
  · intro hit
    exact outside (Generic.pair_product E _ points (Or.inl hit))
  · intro hit
    exact outside (Generic.pair_product E _ points (Or.inr hit))

theorem exists_product_roots (c1 : C1Received) (c2 : C2Received) (E : K[X]) :
    ∃ S : Finset K, ∀ t, t ∈ S ↔
      Admissible t ∧ (productObstruction c1 c2 E).eval t = 0 :=
  MiddleSimplePairMass.exists_complete_root_set (productObstruction c1 c2 E)

set_option maxRecDepth 400 in
theorem product_roots_card (c1 : C1Received) (c2 : C2Received) (E : K[X])
    (nonzero : E ≠ 0) (degree : E.natDegree ≤ 65061549) (S : Finset K)
    (complete : ∀ t, t ∈ S ↔
      Admissible t ∧ (productObstruction c1 c2 E).eval t = 0) :
    S.card ≤ 90407376 := by
  have productBound := product_nonzero_degree c1 c2 E nonzero degree
  exact (MiddleSimplePairMass.complete_roots_card (productObstruction c1 c2 E)
    productBound.1 S complete).trans productBound.2

/-- Keep the large field-cardinality expression abstract; no numeral replay. -/
def pairBudget : ℚ := (90407376 : ℚ) * (90407376-1) /
  ((domainSize : ℚ) * ((domainSize : ℚ)-1))

variable {O H : Type*}

theorem product_pair_mass (coins : Finset O)
    (draw : H → O → Option (K × H)) (between : K → H → H)
    (law : NestedCircleMass.Generic.Uniform coins draw
      (ordinaryAtomMass (FiniteOptionMass.successMass OrdinaryPrefixMass.value)))
    (c1 : C1Received) (c2 : C2Received) (E : K[X])
    (nonzero : E ≠ 0) (degree : E.natDegree ≤ 65061549) (S : Finset K)
    (complete : ∀ t, t ∈ S ↔
      Admissible t ∧ (productObstruction c1 c2 E).eval t = 0) (h : H) :
    targetMass coins draw between S h ≤ pairBudget := by
  have admissible : ∀ t ∈ S, Admissible t := fun t member => ((complete t).mp member).1
  have mass := actual_one_call_target_bound coins draw between law S admissible h
  exact mass.trans (MiddleSimplePairMass.Generic.pair_cap_mono S.card 90407376
    domainSize (product_roots_card c1 c2 E nonzero degree S complete)
    (by omega) domain_size_bounds.2)

/-- Proposed recovery predicate may depend on every later challenge. Its
source instantiation must prove that recovery contains an actual HighPrefix. -/
def residualProbability {q : Nat} (e : Execution q) (recovered : K → K → K → K → Prop)
    (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if higherPrefix e gamma kappa tau alpha ∧ ¬recovered gamma kappa tau alpha
      then suffix e gamma kappa tau alpha A G else 0))))

def highResidualProbability {q : Nat} (e : Execution q)
    (recovered : K → K → K → K → Prop) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if HighPrefix e gamma kappa tau alpha ∧ ¬recovered gamma kappa tau alpha
      then suffix e gamma kappa tau alpha A G else 0))))

theorem pointwise_partition {q : Nat} (e : Execution q)
    (recovered : K → K → K → K → Prop)
    (recovery : ∀ gamma kappa tau alpha, recovered gamma kappa tau alpha →
      HighPrefix e gamma kappa tau alpha) (gamma kappa tau alpha : K) (A G : Finset K) :
    (if higherPrefix e gamma kappa tau alpha ∧ ¬recovered gamma kappa tau alpha
      then suffix e gamma kappa tau alpha A G else 0) =
      (if HighPrefix e gamma kappa tau alpha ∧ ¬recovered gamma kappa tau alpha
        then suffix e gamma kappa tau alpha A G else 0) +
      (if LowPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0) := by
  have partition := higher_partition e gamma kappa tau alpha
  by_cases recoveredHere : recovered gamma kappa tau alpha
  · have high := recovery gamma kappa tau alpha recoveredHere
    have notLow : ¬LowPrefix e gamma kappa tau alpha := fun low => low.2 high
    simp only [recoveredHere, not_true_eq_false, and_false, if_false,
      if_neg notLow, zero_add]
  · by_cases high : HighPrefix e gamma kappa tau alpha
    · have higher := partition.mpr (Or.inl high)
      have notLow : ¬LowPrefix e gamma kappa tau alpha := fun low => low.2 high
      simp only [recoveredHere, not_false_eq_true, and_true, if_pos higher,
        if_pos high, if_neg notLow, add_zero]
    · by_cases low : LowPrefix e gamma kappa tau alpha
      · have higher := partition.mpr (Or.inr low)
        simp only [recoveredHere, not_false_eq_true, and_true, if_pos higher,
          if_neg high, if_pos low, zero_add]
      · have notHigher : ¬higherPrefix e gamma kappa tau alpha := by
          intro higher
          exact (partition.mp higher).elim high low
        simp only [recoveredHere, not_false_eq_true, and_true, if_neg notHigher,
          if_neg high, if_neg low, zero_add]

theorem probability_partition {q : Nat} (e : Execution q)
    (recovered : K → K → K → K → Prop)
    (recovery : ∀ gamma kappa tau alpha, recovered gamma kappa tau alpha →
      HighPrefix e gamma kappa tau alpha) (A G Gamma : Finset K) :
    residualProbability e recovered A G Gamma = highResidualProbability e recovered A G Gamma +
      lowProbability e A G Gamma := by
  unfold residualProbability highResidualProbability lowProbability lowSlice
  simp_rw [pointwise_partition e recovered recovery, avg_add]

/-- Only LOW spends a suffix repair. The high-residual cardinal estimate
is explicit until the SAME-Q recovery event adapter has been supplied. -/
theorem conditional_nonpair_bound {q : Nat} (e : Execution q)
    (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (largeGamma : 6752623450 ≤ Gamma.card) (positive : 0 < q) (count : q ≤ 262144)
    (E : K[X])
    (outside : ¬∀ r, (productObstruction e.c1 e.c2 E).eval
      (SelectedOODGate.point e.data r) = 0)
    (recovered : K → K → K → K → Prop)
    (recovery : ∀ gamma kappa tau alpha, recovered gamma kappa tau alpha →
      HighPrefix e gamma kappa tau alpha)
    (highBound : highResidualProbability e recovered A G Gamma ≤ (104 : ℚ)/Gamma.card) :
    residualProbability e recovered A G Gamma ≤ (117153 : ℚ)/Gamma.card +
      integratedBudget q Gamma A + (q : ℚ)/G.card + 18/A.card := by
  have lowOutside := (product_outside e.c1 e.c2 E (SelectedOODGate.point e.data) outside).2
  have low := low_probability_bound e checked circles west A G Gamma ha hg hgamma
    largeGamma positive count lowOutside
  rw [probability_partition e recovered recovery]
  have bounded := add_le_add highBound low
  have combine : (104 : ℚ)/Gamma.card + (117049 : ℚ)/Gamma.card =
      (117153 : ℚ)/Gamma.card := by rw [← add_div]; norm_num
  calc
    _ ≤ (104 : ℚ)/Gamma.card + ((117049 : ℚ)/Gamma.card +
        integratedBudget q Gamma A + (q : ℚ)/G.card + 18/A.card) := bounded
    _ = _ := by rw [← add_assoc, ← add_assoc, ← add_assoc, combine]

/-- Arbitrary terminal-history continuation. This consumes, rather than
invents, its source/event domination. Aborts retain zero payoff and the
history-uniform law is an explicit assumption. -/
theorem conditional_continuation_bound (coins : Finset O) (coinNonempty : coins.Nonempty)
    (draw : H → O → Option (K × H)) (between : K → H → H)
    (law : NestedCircleMass.Generic.Uniform coins draw
      (ordinaryAtomMass (FiniteOptionMass.successMass OrdinaryPrefixMass.value)))
    (c1 : C1Received) (c2 : C2Received) (E : K[X])
    (nonzero : E ≠ 0) (degree : E.natDegree ≤ 65061549) (S : Finset K)
    (complete : ∀ t, t ∈ S ↔
      Admissible t ∧ (productObstruction c1 c2 E).eval t = 0)
    (reward : K → K → H → ℚ) (b : ℚ) (bNonnegative : 0 ≤ b)
    (sourceEvent : ∀ first second terminal,
      Admissible first → Admissible second → second ≠ first →
      reward first second terminal ≤ (if (first, second) ∈ S.offDiag then 1 else 0)+b)
    (h : H) :
    NestedCircleContinuation.Generic.pairPay coins draw Admissible between reward h ≤
      pairBudget+b := by
  have bound := NestedCircleContinuation.actual_exception_bound coins coinNonempty draw
    between S reward b bNonnegative sourceEvent h
  apply bound.trans
  simpa only [add_comm] using add_le_add_right
    (product_pair_mass coins draw between law c1 c2 E nonzero degree S complete h) b

#print axioms Generic.pair_product
#print axioms Generic.gated_partition
#print axioms product_nonzero_degree
#print axioms product_outside
#print axioms exists_product_roots
#print axioms product_roots_card
#print axioms product_pair_mass
#print axioms pointwise_partition
#print axioms probability_partition
#print axioms conditional_nonpair_bound
#print axioms conditional_continuation_bound
end
end AspisV8.ResidualRecoveryComposition
