import SelectedQuadraticCover
import CausalFactorReduction

/-! Accepted compact-suffix mass on the SAME quadratic factor branch.
The OOD indicator is kept explicit: this file averages fresh gamma and
later causal responses, not the two OOD points or a Fiat-Shamir oracle.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.CausalQuadraticReduction
noncomputable section
open Polynomial Finset
open AspisV8.SelectedReceivedOracle AspisV8.CausalCoveredRecovery
open AspisV8.SelectedCoveredRelation
open AspisV8.CausalFactorReduction AspisV8.SelectedFactorCoherence
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.JointImageGame AspisV8.RelationCompatibleMoment
open AspisV8.GammaComponentGame AspisV8.ComponentOODBinding
open AspisV8.SelectedOODGate AspisV8.CausalOrderedRelation
open AspisV8.QuotientFamilySelected AspisV5ComponentCConcreteFoldLinearity
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7Tag73ExactGRSConversion
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
attribute [local irreducible] curvePrimeFactors

def quadraticRoot {q : Nat} (e : Execution q) (gamma : K) (Q : Fin 1024 → K) : Prop :=
  ∃ F ∈ curvePrimeFactors (parent e.c1 e.c2), F.natDegree = 2 ∧
    (∀ r, FactorCoherence.pointSubstitution (point e.data r)
      (CurveOODGate.answerCurve (answers e.data r)) F = 0) ∧
    challengeCandidateHom gamma
      (exactCircleGRSPolynomial ((atGamma e.data gamma).original Q)) F = 0

def quadraticPrefix {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) : Prop :=
  factorPrefix e gamma kappa tau alpha ∧
    ∃ Q ∈ literalFamily (e.raw gamma), ¬badAnchor (e.rows gamma) Q ∧
      (e.strategy gamma kappa).final tau alpha = coefficientFoldLayer 256 alpha Q ∧
      quadraticRoot e gamma Q

def quadraticSlice {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if quadraticPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0)))

def residualSlice {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if factorPrefix e gamma kappa tau alpha ∧ ¬quadraticPrefix e gamma kappa tau alpha
      then suffix e gamma kappa tau alpha A G else 0)))

def quadraticProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => quadraticSlice e gamma A G)
def residualProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => residualSlice e gamma A G)

theorem partition {q : Nat} (e : Execution q) (A G Gamma : Finset K) :
    factorProbability e A G Gamma = quadraticProbability e A G Gamma + residualProbability e A G Gamma := by
  unfold factorProbability quadraticProbability residualProbability factorSlice quadraticSlice residualSlice
  simp_rw [← avg_add]
  congr 1
  funext gamma
  congr 1
  funext kappa
  congr 1
  funext tau
  congr 1
  funext alpha
  by_cases quad : quadraticPrefix e gamma kappa tau alpha
  · have factor := quad.1
    simp only [quad, factor, if_true, not_true_eq_false, and_false, if_false, add_zero]
  · by_cases factor : factorPrefix e gamma kappa tau alpha
    · simp only [quad, factor, if_false, if_true, not_false_eq_true, and_self, zero_add]
    · simp only [quad, factor, if_false, false_and, zero_add]

theorem slice_unit {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (count : q ≤ 262144) : quadraticSlice e gamma A G ≤ 1 := by
  have count' : q ≤ domain.card := by rw [domain_card]; exact count
  unfold quadraticSlice
  apply avg_le G hg
  intro kappa _
  apply avg_le G hg
  intro tau _
  apply avg_le A ha
  intro alpha _
  split_ifs
  · exact CausalOrderedRelation.after_unit ((e.rows gamma).before kappa)
      e.quarterChecked (oracle 0 (e.raw gamma)) (e.strategy gamma kappa)
      tau alpha A G ha hg count'
  · norm_num

/-- The construction is outside the quantification over all OOD data and
all later strategies sharing these fixed C1/C2 words. -/
theorem exists_quadratic_bound (c1 : C1Received) (c2 : C2Received) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ 114687 ∧
      ∀ {q : Nat} (e : Execution q), e.c1 = c1 → e.c2 = c2 →
      ∀ (A G Gamma : Finset K), A.Nonempty → G.Nonempty → Gamma.Nonempty → q ≤ 262144 →
      quadraticProbability e A G Gamma ≤
        (if ∀ r, E.eval (point e.data r) = 0 then 1 else 0) + 936616/(Gamma.card:ℚ) := by
  obtain ⟨E, B, en, ed, bc, cover⟩ := SelectedQuadraticCover.fixed_cover c1 c2
  refine ⟨E, en, ed, ?_⟩
  intro q e ec1 ec2 A G Gamma ha hg hgamma count
  by_cases roots : ∀ r, E.eval (point e.data r) = 0
  · have bound := avg_le Gamma hgamma _ _ (fun gamma _ => slice_unit e gamma A G ha hg count)
    change quadraticProbability e A G Gamma ≤ 1 at bound
    simp only [if_pos roots]
    exact bound.trans (le_add_of_nonneg_right (by positivity))
  · have outside : ∀ gamma ∈ Gamma, gamma ∉ Gamma ∩ B → quadraticSlice e gamma A G = 0 := by
      intro gamma member notB
      have noPrefix : ∀ kappa tau alpha, ¬quadraticPrefix e gamma kappa tau alpha := by
        intro kappa tau alpha ⟨_, Q, _, _, _, qr⟩
        have covered := cover (point e.data)
          (fun r => CurveOODGate.answerCurve (answers e.data r)) gamma
          (exactCircleGRSPolynomial ((atGamma e.data gamma).original Q))
        have qr' : ∃ F ∈ curvePrimeFactors (parent c1 c2), F.natDegree = 2 ∧
            (∀ r, FactorCoherence.pointSubstitution (point e.data r)
              (CurveOODGate.answerCurve (answers e.data r)) F = 0) ∧
            challengeCandidateHom gamma
              (exactCircleGRSPolynomial ((atGamma e.data gamma).original Q)) F = 0 := by
          simpa only [quadraticRoot, ec1, ec2] using qr
        exact notB (Finset.mem_inter.mpr ⟨member, (covered qr').resolve_left roots⟩)
      simp only [quadraticSlice, noPrefix, if_false, avg, Finset.sum_const_zero, zero_div]
    have bound := avg_exception Gamma (Gamma ∩ B) hgamma (Finset.inter_subset_left)
      (fun gamma => quadraticSlice e gamma A G) 0 (by norm_num)
      (fun gamma _ => slice_unit e gamma A G ha hg count)
      (fun gamma member notB => le_of_eq (outside gamma member notB))
    have size : (Gamma ∩ B).card ≤ 936616 := (Finset.card_le_card Finset.inter_subset_right).trans bc
    have sizeQ : ((Gamma ∩ B).card : ℚ) ≤ 936616 := by exact_mod_cast size
    simp only [add_zero] at bound
    simp only [if_neg roots, zero_add]
    exact bound.trans (div_le_div_of_nonneg_right sizeQ (Nat.cast_nonneg Gamma.card))

/-- Existing missing-good and factor-cover charges are used once. The
remaining accepted factor mass is defined by an explicit complementary
prefix, not discarded or called extraction success. -/
theorem exists_total_reduction (c1 : C1Received) (c2 : C2Received) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ 114687 ∧
      ∀ {q : Nat} (e : Execution q), e.c1 = c1 → e.c2 = c2 →
      e.data.Checked →
      (e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1) →
      (∀ r, pointX e.data r ≠ -1) →
      ∀ (A G Gamma : Finset K), A.Nonempty → G.Nonempty → Gamma.Nonempty →
      0 < q → q ≤ 262144 →
      totalProbability e A G Gamma ≤
        ceiling q A G + 117077/(Gamma.card:ℚ) +
        ((if ∀ r, E.eval (point e.data r) = 0 then 1 else 0) + 936616/(Gamma.card:ℚ)) +
        residualProbability e A G Gamma := by
  obtain ⟨E, en, ed, bounded⟩ := exists_quadratic_bound c1 c2
  refine ⟨E, en, ed, ?_⟩
  intro q e ec1 ec2 checked circles west A G Gamma ha hg hgamma positive count
  have old := CausalFactorReduction.total_reduction e checked circles west A G Gamma
    ha hg hgamma positive count
  have split := partition e A G Gamma
  have quadratic := bounded e ec1 ec2 A G Gamma ha hg hgamma count
  linarith only [old, split, quadratic]

#print axioms partition
#print axioms slice_unit
#print axioms exists_quadratic_bound
#print axioms exists_total_reduction
end
end AspisV8.CausalQuadraticReduction
