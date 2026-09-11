import NestedCircleContinuationV2
import SelectedMiddleGammaCover
import MiddleSimplePairMassV4
import SelectedHigherYProbability

/-! Abort-preserving OOD-pair / uniform-gamma composition for the actual
high-support higher-Y event. The terminal callback retains its full history,
and the suffix appears exactly once inside the existing highProbability.
The ordinary law is history-uniform by hypothesis; no ROM freshness or
literal controller refinement is asserted here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedMiddleGammaProbability
open Polynomial Finset
open AspisV8.JointImageGame AspisV8.RelationCompatibleMoment
open AspisV8.SelectedReceivedOracle AspisV8.CausalCoveredRecovery
open AspisV8.CausalOrderedRelation AspisV8.SelectedHigherYHighSupport
open AspisV8.SelectedHigherYProbability AspisV8.SelectedMiddleGammaCover
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.OODInterpolant AspisV8.GammaComponentGame
open AspisV8.SecureCircleParameterDomain AspisV8.NestedCircleMass
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- Source-coordinate hypotheses for the execution extracted from one
successful terminal history. They do not identify histories having the same
pair. C1/C2 are the same words fixed before either draw. -/
structure SourceAt {q : Nat} (c1 : C1Received) (c2 : C2Received)
    (first second : K) (e : Execution q) : Prop where
  c1_fixed : e.c1 = c1
  c2_fixed : e.c2 = c2
  checked : e.data.Checked
  circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1
  west : ∀ r, ComponentOODBinding.pointX e.data r ≠ -1
  point_first : SelectedOODGate.point e.data 0 = first
  point_second : SelectedOODGate.point e.data 1 = second

theorem high_indicator {q : Nat} (e : Execution q) (Gamma : Finset K)
    (gamma kappa tau alpha : K) (inside : gamma ∈ Gamma)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (count : q ≤ 262144) :
    (if HighPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0) ≤
      if gamma ∈ middleGammas e.c1 e.c2 e.data Gamma then (1 : ℚ) else 0 := by
  by_cases high : HighPrefix e gamma kappa tau alpha
  · have member := SelectedMiddleGammaCover.high_prefix_mem e Gamma gamma kappa tau alpha inside high
    rw [if_pos high, if_pos member]
    exact after_unit ((e.rows gamma).before kappa) e.quarterChecked
      (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha A G ha hg
      (by rwa [domain_card])
  · rw [if_neg high]
    split_ifs <;> norm_num

/-- Uniformity is the displayed original Gamma mean, not a conditional
mean on regular or nonexceptional challenges. All later histories survive. -/
theorem high_card_bound {q : Nat} (e : Execution q) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (count : q ≤ 262144) :
    highProbability e A G Gamma ≤
      ((middleGammas e.c1 e.c2 e.data Gamma).card : ℚ)/Gamma.card := by
  have bound := avg_mono Gamma (fun gamma => highSlice e gamma A G)
    (fun gamma => if gamma ∈ middleGammas e.c1 e.c2 e.data Gamma then (1 : ℚ) else 0)
    (by
      intro gamma inside
      apply avg_le G hg
      intro kappa _
      apply avg_le G hg
      intro tau _
      apply avg_le A ha
      intro alpha _
      exact high_indicator e Gamma gamma kappa tau alpha inside A G ha hg count)
  rw [RegularQueryMoment.Generic.avg_indicator] at bound
  have same : Gamma.filter (fun gamma => gamma ∈ middleGammas e.c1 e.c2 e.data Gamma) =
      middleGammas e.c1 e.c2 e.data Gamma := by
    ext gamma
    constructor
    · intro member
      exact (Finset.mem_filter.mp member).2
    · intro member
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp member).1, member⟩
  rw [same] at bound
  exact bound

/-- On pair-root histories the SAME actual suffix, rather than a scalar
acceptance proxy, is bounded by one. No second suffix charge is introduced. -/
theorem high_unit {q : Nat} (e : Execution q) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (count : q ≤ 262144) : highProbability e A G Gamma ≤ 1 := by
  apply avg_le Gamma hgamma
  intro gamma _
  apply avg_le G hg
  intro kappa _
  apply avg_le G hg
  intro tau _
  apply avg_le A ha
  intro alpha _
  by_cases high : HighPrefix e gamma kappa tau alpha
  · rw [if_pos high]
    exact after_unit ((e.rows gamma).before kappa) e.quarterChecked
      (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha A G ha hg
      (by rwa [domain_card])
  · rw [if_neg high]
    norm_num

/-- The same pre-OOD E from the selected cover bounds every terminal
history. The data/answer functions need not collapse to functions of the pair. -/
theorem terminal_bound {q : Nat} (c1 : C1Received) (c2 : C2Received)
    (A G Gamma : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hgamma : Gamma.Nonempty) (count : q ≤ 262144)
    (E : K[X])
    (cover : ∀ d : Data (K := K), d.Checked →
      (d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1) →
      (∀ r, ComponentOODBinding.pointX d r ≠ -1) →
      (∀ r, E.eval (SelectedOODGate.point d r)=0) ∨
        (middleGammas c1 c2 d Gamma).card ≤ 117145)
    (S : Finset K) (complete : ∀ t, t ∈ S ↔ Admissible t ∧ E.eval t=0)
    (first second : K) (e : Execution q) (source : SourceAt c1 c2 first second e)
    (firstGood : Admissible first) (secondGood : Admissible second)
    (different : second ≠ first) :
    highProbability e A G Gamma ≤
      (if (first, second) ∈ S.offDiag then 1 else 0)+(117145 : ℚ)/Gamma.card := by
  have budgetNonnegative : (0 : ℚ) ≤ (117145 : ℚ)/Gamma.card := by positivity
  by_cases pair : (first, second) ∈ S.offDiag
  · rw [if_pos pair]
    exact (high_unit e A G Gamma ha hg hgamma count).trans
      (le_add_of_nonneg_right budgetNonnegative)
  · rw [if_neg pair, zero_add]
    rcases cover e.data source.checked source.circles source.west with roots | small
    · have firstRoot : E.eval first=0 := by
        simpa only [source.point_first] using roots 0
      have secondRoot : E.eval second=0 := by
        simpa only [source.point_second] using roots 1
      exact False.elim (pair (Finset.mem_offDiag.mpr
        ⟨(complete first).mpr ⟨firstGood, firstRoot⟩,
         (complete second).mpr ⟨secondGood, secondRoot⟩, Ne.symm different⟩))
    · have actualSmall : (middleGammas e.c1 e.c2 e.data Gamma).card ≤ 117145 := by
        simpa only [source.c1_fixed, source.c2_fixed] using small
      exact (high_card_bound e A G Gamma ha hg count).trans
        (div_le_div_of_nonneg_right (Nat.cast_le.mpr actualSmall) (Nat.cast_nonneg _))

variable {O H : Type*}

/-- Exact continuation-valued event. `finish` uses the actual terminal
history after all distinct retries; the gamma mean occurs only afterward. -/
def eventMass {q : Nat} (coins : Finset O) (draw : H → O → Option (K × H))
    (between : K → H → H) (finish : K → K → H → Execution q)
    (A G Gamma : Finset K) (h : H) : ℚ :=
  NestedCircleContinuation.Generic.pairPay coins draw Admissible between
    (fun first second terminal => highProbability (finish first second terminal) A G Gamma) h

/-- Composition for an arbitrary SAME E supplied with its cover. Immediate
ordinary failures and exhausted retries contribute zero; history-uniformity
is explicit, not inferred from labels or from this event definition. -/
theorem probability_of_cover {q : Nat} (c1 : C1Received) (c2 : C2Received)
    (A G Gamma : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hgamma : Gamma.Nonempty) (count : q ≤ 262144)
    (E : K[X]) (nonzero : E ≠ 0) (degree : E.natDegree ≤ 65061549)
    (cover : ∀ d : Data (K := K), d.Checked →
      (d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1) →
      (∀ r, ComponentOODBinding.pointX d r ≠ -1) →
      (∀ r, E.eval (SelectedOODGate.point d r)=0) ∨
        (middleGammas c1 c2 d Gamma).card ≤ 117145)
    (coins : Finset O) (nonempty : coins.Nonempty)
    (draw : H → O → Option (K × H)) (between : K → H → H)
    (law : NestedCircleMass.Generic.Uniform coins draw
      (ordinaryAtomMass (FiniteOptionMass.successMass OrdinaryPrefixMass.value)))
    (finish : K → K → H → Execution q)
    (source : ∀ first second terminal, Admissible first → Admissible second → second ≠ first →
      SourceAt c1 c2 first second (finish first second terminal)) (h : H) :
    eventMass coins draw between finish A G Gamma h ≤
      (65061549 : ℚ)*65061548 /
        ((RootSetPairMass.domainSize : ℚ)*((RootSetPairMass.domainSize : ℚ)-1))+
        (117145 : ℚ)/Gamma.card := by
  obtain ⟨S, complete⟩ := MiddleSimplePairMass.exists_complete_root_set E
  have bound := NestedCircleContinuation.actual_exception_bound coins nonempty draw between S
    (fun first second terminal => highProbability (finish first second terminal) A G Gamma)
    ((117145 : ℚ)/Gamma.card) (by positivity)
    (fun first second terminal firstGood secondGood different =>
      terminal_bound c1 c2 A G Gamma ha hg hgamma count E cover S complete first second
        (finish first second terminal) (source first second terminal firstGood secondGood different)
        firstGood secondGood different) h
  have pair := MiddleSimplePairMass.pair_root_mass_numeric_le coins draw between law E
    nonzero degree S complete h
  exact bound.trans (add_le_add pair le_rfl)

/-- The chosen E depends only on fixed C1/C2 and the original Gamma set,
before both OOD draws. No early-C1 success, regularity, own-support, candidate
membership or independent-pair premise is added at this probability boundary. -/
theorem probability_bound {q : Nat} (c1 : C1Received) (c2 : C2Received)
    (A G Gamma : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hgamma : Gamma.Nonempty) (count : q ≤ 262144)
    (coins : Finset O) (nonempty : coins.Nonempty)
    (draw : H → O → Option (K × H)) (between : K → H → H)
    (law : NestedCircleMass.Generic.Uniform coins draw
      (ordinaryAtomMass (FiniteOptionMass.successMass OrdinaryPrefixMass.value)))
    (finish : K → K → H → Execution q)
    (source : ∀ first second terminal, Admissible first → Admissible second → second ≠ first →
      SourceAt c1 c2 first second (finish first second terminal)) (h : H) :
    eventMass coins draw between finish A G Gamma h ≤
      (65061549 : ℚ)*65061548 /
        ((RootSetPairMass.domainSize : ℚ)*((RootSetPairMass.domainSize : ℚ)-1))+
        (117145 : ℚ)/Gamma.card := by
  obtain ⟨E, nonzero, degree, cover⟩ := SelectedMiddleGammaCover.exists_selected_cover c1 c2 Gamma
  exact probability_of_cover c1 c2 A G Gamma ha hg hgamma count E nonzero degree cover
    coins nonempty draw between law finish source h

#print axioms high_indicator
#print axioms high_card_bound
#print axioms high_unit
#print axioms terminal_bound
#print axioms probability_of_cover
#print axioms probability_bound
end
end AspisV8.SelectedMiddleGammaProbability
