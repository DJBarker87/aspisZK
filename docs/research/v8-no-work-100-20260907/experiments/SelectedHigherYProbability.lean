import SelectedRegularLowProbability

/-! Source-review draft: exact high/low partition of the SAME selected
higher-Y suffix. Fixed early C1 controls the high-support gamma set; the
checked common-row layer cake controls the low branch. Final selection
remains adaptive in tau/alpha. Only the low branch incurs a shared suffix
repair, once. The nonzero Gamma domain and pre-OOD pair-root alternative
remain explicit; no sampler, Fiat--Shamir or global acceptance claim.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedHigherYProbability
open Polynomial Finset
open AspisV8.JointImageGame AspisV8.RelationCompatibleMoment
open AspisV8.SelectedReceivedOracle AspisV8.CausalCoveredRecovery
open AspisV8.CausalOrderedRelation AspisV8.ComponentOODBinding
open AspisV8.SelectedHigherYBranch AspisV8.SelectedHigherYHighSupport
open AspisV8.EarlyC1Projection AspisV8.EarlyC1HigherYSupport
open AspisV8.SelectedRegularLayerCakeInstance AspisV8.SelectedRegularLowProbability
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

def highSlice {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if HighPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0)))

def higherSlice {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if higherPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0)))

def highProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => highSlice e gamma A G)

def higherProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => higherSlice e gamma A G)

theorem prefix_disjoint {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) :
    ¬(HighPrefix e gamma kappa tau alpha ∧ LowPrefix e gamma kappa tau alpha) := by
  rintro ⟨high, low⟩
  exact low.2 high

/-- Exact weighted partition; the two indicators multiply the identical
actual suffix value, without changing the selected final or continuation. -/
theorem pointwise_partition {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (A G : Finset K) :
    (if higherPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0) =
      (if HighPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0)+
      (if LowPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0) := by
  have partition := higher_partition e gamma kappa tau alpha
  by_cases high : HighPrefix e gamma kappa tau alpha
  · have higher := partition.mpr (Or.inl high)
    have notLow : ¬LowPrefix e gamma kappa tau alpha := fun low => low.2 high
    simp only [if_pos higher, if_pos high, if_neg notLow, add_zero]
  · by_cases low : LowPrefix e gamma kappa tau alpha
    · have higher := partition.mpr (Or.inr low)
      simp only [if_pos higher, if_neg high, if_pos low, zero_add]
    · have notHigher : ¬higherPrefix e gamma kappa tau alpha := by
        intro higher
        exact (partition.mp higher).elim high low
      simp only [if_neg notHigher, if_neg high, if_neg low, zero_add]

theorem slice_partition {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K) :
    higherSlice e gamma A G = highSlice e gamma A G+lowSlice e gamma A G := by
  unfold higherSlice highSlice lowSlice
  simp_rw [← avg_add]
  congr 1
  funext kappa
  congr 1
  funext tau
  congr 1
  funext alpha
  exact pointwise_partition e gamma kappa tau alpha A G

theorem probability_partition {q : Nat} (e : Execution q) (A G Gamma : Finset K) :
    higherProbability e A G Gamma = highProbability e A G Gamma+lowProbability e A G Gamma := by
  unfold higherProbability highProbability lowProbability
  simp_rw [slice_partition]
  exact avg_add Gamma _ _

/-- The SAME actual high witness enters the fixed gamma set. Inside that
set its actual compact suffix is bounded by one, not by a scalar proxy. -/
theorem high_prefix_indicator {q : Nat} (e : Execution q) (Gamma : Finset K)
    (gamma kappa tau alpha : K) (inside : gamma ∈ Gamma)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (count : q ≤ 262144) :
    (if HighPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0) ≤
      if gamma ∈ highHigherGammas e.c1 e.c2 e.data Gamma then (1 : ℚ) else 0 := by
  by_cases high : HighPrefix e gamma kappa tau alpha
  · have member := high_prefix_mem e Gamma gamma kappa tau alpha inside high
    rw [if_pos high, if_pos member]
    exact after_unit ((e.rows gamma).before kappa) e.quarterChecked
      (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha A G ha hg
      (by rwa [domain_card])
  · rw [if_neg high]
    split_ifs <;> norm_num

theorem high_slice_indicator {q : Nat} (e : Execution q) (Gamma : Finset K)
    (gamma : K) (inside : gamma ∈ Gamma) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (count : q ≤ 262144) :
    highSlice e gamma A G ≤
      if gamma ∈ highHigherGammas e.c1 e.c2 e.data Gamma then (1 : ℚ) else 0 := by
  apply avg_le G hg
  intro kappa _
  apply avg_le G hg
  intro tau _
  apply avg_le A ha
  intro alpha _
  exact high_prefix_indicator e Gamma gamma kappa tau alpha inside A G ha hg count

/-- The sparse/dense helper dichotomy has already been consumed by
fixed_early_high_count. No maximum over postselected branches or extra
regularity premise is introduced at this probability boundary. -/
theorem high_probability_bound {q : Nat} (e : Execution q) (p : C1Messages)
    (found : earlyC1 e.c1=some p) (checked : e.data.Checked)
    (A G Gamma : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (nonzero : ∀ gamma ∈ Gamma, gamma ≠ 0) (count : q ≤ 262144) :
    highProbability e A G Gamma ≤ (117077 : ℚ)/Gamma.card := by
  have bound := avg_mono Gamma _ _ (fun gamma inside =>
    high_slice_indicator e Gamma gamma inside A G ha hg count)
  rw [RegularQueryMoment.Generic.avg_indicator] at bound
  have same : Gamma.filter (fun gamma => gamma ∈ highHigherGammas e.c1 e.c2 e.data Gamma) =
      highHigherGammas e.c1 e.c2 e.data Gamma := by
    ext gamma
    constructor
    · intro member
      exact (Finset.mem_filter.mp member).2
    · intro member
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp member).1, member⟩
  rw [same] at bound
  have card := fixed_early_high_count e.c1 p e.c2 Gamma nonzero found e.data checked
  exact bound.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr card) (Nat.cast_nonneg _))

/-- Actual higher-Y mass, conditional on the explicit early-C1 success
and outside-pair-root hypotheses. The high and low masses add disjointly;
the low branch contributes the ONLY suffix repair term. -/
theorem higher_probability_bound {q : Nat} (e : Execution q) (p : C1Messages)
    (found : earlyC1 e.c1=some p) (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (nonzero : ∀ gamma ∈ Gamma, gamma ≠ 0)
    (largeGamma : 6752623450 ≤ Gamma.card) (positive : 0 < q) (count : q ≤ 262144)
    (outside : ¬∀ r, (SelectedSingularOODFamily.obstruction e.c1 e.c2).eval
      (SelectedOODGate.point e.data r)=0) :
    higherProbability e A G Gamma ≤ ((117077+117049 : ℚ)/Gamma.card) +
      integratedBudget q Gamma A+(q : ℚ)/G.card+18/A.card := by
  rw [probability_partition]
  have high := high_probability_bound e p found checked A G Gamma ha hg nonzero count
  have low := low_probability_bound e checked circles west A G Gamma ha hg hgamma
    largeGamma positive count outside
  simpa only [add_div, add_assoc] using add_le_add high low

#print axioms prefix_disjoint
#print axioms pointwise_partition
#print axioms probability_partition
#print axioms high_prefix_indicator
#print axioms high_probability_bound
#print axioms higher_probability_bound
end
end AspisV8.SelectedHigherYProbability
