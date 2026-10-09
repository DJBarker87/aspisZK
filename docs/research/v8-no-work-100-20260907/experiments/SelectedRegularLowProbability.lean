import SelectedRegularLayerCakeInstance

/-! Source-review draft: integrate the literal low higher-Y compact-suffix
event over the original gamma/kappa/tau/alpha means. One common-row root
set costs at most 117049/|Gamma|, using the actual suffix unit bound.
One shared suffix repair is charged to the whole union, not each factor.
The pre-OOD pair-root alternative is an explicit hypothesis, not a sampler
or Fiat--Shamir theorem. No domain is conditioned on passing an event.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedRegularLowProbability
open Polynomial Finset
open AspisV8.JointImageGame AspisV8.RelationCompatibleMoment
open AspisV8.SelectedReceivedOracle AspisV8.CausalCoveredRecovery
open AspisV8.CausalOrderedRelation AspisV8.ComponentOODBinding
open AspisV8.SelectedHigherYHighSupport AspisV8.SelectedRegularLowSupport
open AspisV8.SelectedRegularLayerCakeInstance AspisV8.SelectedFactorCoherence
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

def lowSlice {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if LowPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0)))

def lowProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => lowSlice e gamma A G)

def momentSlice {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (gamma : K) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    unionScore e r Z gamma kappa tau alpha)))

def repair (q : Nat) (A G : Finset K) : ℚ := (q : ℚ)/G.card+18/A.card

/-- The quantity bounded on root histories is the SAME actual suffix
probability, with its low-event indicator. It is not a scalar test proxy. -/
theorem low_slice_unit {q : Nat} (e : Execution q) (gamma : K)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (count : q ≤ 262144) :
    lowSlice e gamma A G ≤ 1 := by
  apply avg_le G hg
  intro kappa _
  apply avg_le G hg
  intro tau _
  apply avg_le A ha
  intro alpha _
  by_cases low : LowPrefix e gamma kappa tau alpha
  · rw [if_pos low]
    exact after_unit ((e.rows gamma).before kappa) e.quarterChecked
      (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha A G ha hg
      (by rwa [domain_card])
  · simp only [if_neg low, zero_le_one]

theorem moment_slice_nonneg {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (gamma : K) (A G : Finset K) : 0 ≤ momentSlice e r Z gamma A G := by
  apply avg_nonneg
  intro kappa _
  apply avg_nonneg
  intro tau _
  apply avg_nonneg
  intro alpha _
  unfold unionScore
  split_ifs
  · exact prefixMoment_nonneg e gamma kappa tau alpha
  · exact le_refl _

/-- Shared repair only outside the common root set. On these histories
the literal low event equals the actual regular-low union. -/
theorem nonroot_slice_bound {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (gamma : K) (nonroot : Z.eval gamma ≠ 0)
    (included : ∀ kappa tau alpha, LowPrefix e gamma kappa tau alpha →
      regularLowUnion e r gamma kappa tau alpha)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (positive : 0 < q) (count : q ≤ 262144) :
    lowSlice e gamma A G ≤ momentSlice e r Z gamma A G+repair q A G := by
  have localBound (kappa : K) :
      avg G (fun tau => avg A (fun alpha =>
        if LowPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0)) ≤
      avg G (fun tau => avg A (fun alpha => unionScore e r Z gamma kappa tau alpha))+
        repair q A G := by
    have same : (fun tau => avg A (fun alpha =>
        if LowPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0)) =
        (fun tau => avg A (fun alpha =>
        if regularLowUnion e r gamma kappa tau alpha then suffix e gamma kappa tau alpha A G
        else 0)) := by
      funext tau
      congr 1
      funext alpha
      by_cases low : LowPrefix e gamma kappa tau alpha
      · simp only [if_pos low, if_pos (included kappa tau alpha low)]
      · have absent : ¬regularLowUnion e r gamma kappa tau alpha := by
          rintro ⟨F, _, _, selected⟩
          exact low selected.1
        simp only [if_neg low, if_neg absent]
    have bound := shared_suffix e r gamma kappa A G ha hg positive count
    rw [← same] at bound
    have momentSame : (fun tau => avg A (fun alpha =>
        if regularLowUnion e r gamma kappa tau alpha then
          prefixMoment e gamma kappa tau alpha else 0)) =
        (fun tau => avg A (fun alpha => unionScore e r Z gamma kappa tau alpha)) := by
      funext tau
      congr 1
      funext alpha
      by_cases regular : regularLowUnion e r gamma kappa tau alpha
      · have event : Z.eval gamma ≠ 0 ∧ regularLowUnion e r gamma kappa tau alpha :=
          ⟨nonroot, regular⟩
        simp only [unionScore, if_pos event, if_pos regular]
      · have absent : ¬(Z.eval gamma ≠ 0 ∧ regularLowUnion e r gamma kappa tau alpha) :=
          fun event => regular event.2
        simp only [unionScore, if_neg absent, if_neg regular]
    dsimp only [prefixMoment] at momentSame
    rw [momentSame] at bound
    simpa only [repair, add_assoc] using bound
  have bound := avg_mono G _ _ (fun kappa _ => localBound kappa)
  rw [avg_add, avg_constant G hg] at bound
  exact bound

/-- Finite Fubini on the original product means, not independence inferred
from transcript labels. The supplied bound is uniform in both later values. -/
theorem moment_average_bound {q : Nat} (e : Execution q) (r : Fin 2) (Z : K[X])
    (Gamma A G : Finset K) (hg : G.Nonempty)
    (bounded : ∀ kappa tau,
      TwoTailQueryBound.mean Gamma (fun gamma => TwoTailQueryBound.mean A (fun alpha =>
        unionScore e r Z gamma kappa tau alpha)) ≤ integratedBudget q Gamma A) :
    avg Gamma (fun gamma => momentSlice e r Z gamma A G) ≤ integratedBudget q Gamma A := by
  calc
    avg Gamma (fun gamma => momentSlice e r Z gamma A G) =
        avg G (fun kappa => avg Gamma (fun gamma => avg G (fun tau => avg A (fun alpha =>
          unionScore e r Z gamma kappa tau alpha)))) :=
      RegularQueryMoment.Generic.avg_commute Gamma G _
    _ = avg G (fun kappa => avg G (fun tau => avg Gamma (fun gamma => avg A (fun alpha =>
          unionScore e r Z gamma kappa tau alpha)))) := by
      congr 1
      funext kappa
      exact RegularQueryMoment.Generic.avg_commute Gamma G _
    _ ≤ integratedBudget q Gamma A := by
      apply avg_le G hg
      intro kappa _
      apply avg_le G hg
      intro tau _
      exact bounded kappa tau

/-- Source-shaped actual LOW-branch bound, after all four original finite
averages. There is no supplied representative, support distribution or
regularity premise. The full pre-OOD pair-root alternative stays explicit. -/
theorem low_probability_bound {q : Nat} (e : Execution q) (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (largeGamma : 6752623450 ≤ Gamma.card) (positive : 0 < q) (count : q ≤ 262144)
    (outside : ¬∀ r, (SelectedSingularOODFamily.obstruction e.c1 e.c2).eval
      (SelectedOODGate.point e.data r)=0) :
    lowProbability e A G Gamma ≤ (117049 : ℚ)/Gamma.card +
      integratedBudget q Gamma A+(q : ℚ)/G.card+18/A.card := by
  obtain ⟨r, Z, _, _, roots, included, bounded⟩ := exists_common_row_bound e checked
    circles west Gamma A hgamma ha largeGamma count outside
  have collision : 0 ≤ repair q A G := by unfold repair; positivity
  have pointwise (gamma : K) : lowSlice e gamma A G ≤
      (if Z.eval gamma=0 then (1 : ℚ) else 0)+momentSlice e r Z gamma A G+repair q A G := by
    by_cases root : Z.eval gamma=0
    · rw [if_pos root]
      have unit := low_slice_unit e gamma A G ha hg count
      have nonnegative := moment_slice_nonneg e r Z gamma A G
      linarith only [unit, nonnegative, collision]
    · have bound := nonroot_slice_bound e r Z gamma root
        (fun kappa tau alpha low => included gamma kappa tau alpha root low)
        A G ha hg positive count
      simpa only [if_neg root, zero_add] using bound
  have average := avg_mono Gamma _ _ (fun gamma _ => pointwise gamma)
  rw [avg_add, avg_add, avg_constant Gamma hgamma] at average
  have rootMass : avg Gamma (fun gamma => if Z.eval gamma=0 then (1 : ℚ) else 0) ≤
      (117049 : ℚ)/Gamma.card := by
    rw [RegularQueryMoment.Generic.avg_indicator]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr roots) (Nat.cast_nonneg _)
  have moments := moment_average_bound e r Z Gamma A G hg bounded
  have result := average.trans (add_le_add (add_le_add rootMass moments) (le_refl _))
  simpa only [lowProbability, repair, add_assoc] using result

#print axioms low_slice_unit
#print axioms moment_slice_nonneg
#print axioms nonroot_slice_bound
#print axioms moment_average_bound
#print axioms low_probability_bound
end
end AspisV8.SelectedRegularLowProbability
