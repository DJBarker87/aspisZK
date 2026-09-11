import SelectedMiddleImageRecovery
import SelectedAcceptedPrefixPartitionV2
import SelectedHigherYProbability

/-! Source-review draft. The existing fixed-prefix classification is supplied
with the SAME family/E/beta/sparse set. Outside its pair-root event, an actual
HighPrefix not recovered into that family is supported on at most 104 gammas.
The SAME Q carries Witness, HighSupport, and Recovered; the final remains
adaptive in kappa/tau/alpha. The original Gamma/G/G/A means are unchanged,
and the actual compact suffix occurs once. No FS or authentication claim.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedResidualHighRecovery
open Polynomial Finset
noncomputable section

namespace Generic

/-- Eliminate the three opaque propositions before inserting selected
field/quotient expressions. This adds no representation premise. -/
theorem outcome_recovered {pair exceptional recovered : Prop}
    (outcome : SelectedMiddleImageRecovery.Generic.Outcome pair exceptional recovered)
    (outsidePair : ¬pair) (outsideBad : ¬exceptional) : recovered := by
  cases outcome with
  | pairRoot root => exact False.elim (outsidePair root)
  | exceptional _ hit => exact False.elim (outsideBad hit)
  | recovered _ _ result => exact result

/-- Nonexceptional recovery implies support of its complement on bad.
The bound is on the original mean, including the empty-domain convention. -/
theorem mean_indicator_card {I : Type*} [DecidableEq I]
    (Gamma bad : Finset I) (score : I → ℚ)
    (dominated : ∀ gamma ∈ Gamma,
      score gamma ≤ if gamma ∈ bad then (1 : ℚ) else 0) :
    JointImageGame.avg Gamma score ≤ (bad.card : ℚ)/Gamma.card := by
  classical
  have bound := RelationCompatibleMoment.avg_mono Gamma score
    (fun gamma => if gamma ∈ bad then (1 : ℚ) else 0) dominated
  rw [RegularQueryMoment.Generic.avg_indicator] at bound
  have small : (Gamma.filter fun gamma => gamma ∈ bad).card ≤ bad.card :=
    Finset.card_le_card (fun _ member => (Finset.mem_filter.mp member).2)
  have rational : ((Gamma.filter fun gamma => gamma ∈ bad).card : ℚ) ≤ bad.card :=
    Nat.cast_le.mpr small
  exact bound.trans (div_le_div_of_nonneg_right rational (Nat.cast_nonneg _))
end Generic

open AspisV8.JointImageGame AspisV8.RelationCompatibleMoment
open AspisV8.CausalCoveredRecovery AspisV8.CausalOrderedRelation
open AspisV8.SelectedHigherYHighSupport AspisV8.SelectedRegularLowSupport
open AspisV8.SelectedReceivedOracle AspisV8.ComponentOODBinding
open AspisV8.SelectedMiddleImageRecovery
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev Tuple := Fin 29 → Fin 1024 → K
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- Recovery is tied to the actual high-prefix witness, including its
post-alpha final equality, rather than an unrelated image polynomial. -/
def RecoveredHigh {q : Nat} (e : Execution q) (family : Finset Tuple)
    (gamma kappa tau alpha : K) : Prop :=
  ∃ Q, Witness e gamma kappa tau alpha Q ∧ HighSupport (e.raw gamma) Q ∧
    Recovered e.c1 e.c2 family e.data gamma Q

theorem recovered_high_implies_high {q : Nat} (e : Execution q) (family : Finset Tuple)
    (gamma kappa tau alpha : K)
    (recovered : RecoveredHigh e family gamma kappa tau alpha) :
    HighPrefix e gamma kappa tau alpha := by
  obtain ⟨Q, witness, high, _⟩ := recovered
  exact ⟨Q, witness, high⟩

/-- Restore HighSupport for the SAME Q returned by high_same_quotient.
Only the already checked full/bad partition and small integer arithmetic
are used; the received word is not assumed polynomial. -/
theorem high_support_of_fibre_count (received : Fin 1048576 → K)
    (Q : Fin 1024 → K) (enough : 200808 ≤ fibreCount received Q) :
    HighSupport received Q := by
  have partition := SelectedMiddleGammaCover.full_bad_partition received Q
  change (PartialFoldRecovery.fibreBad (m := 262144)
    (AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder Q) received).card ≤ 4*15334
  omega

/-- Supplied classification is one completed-OOD-prefix object, before
gamma. The bad-set equality names exactly its shared/sparse/insufficient-own
union. No existential package is reconstructed at this interface. -/
theorem high_recovered {q : Nat} (e : Execution q) (Gamma : Finset K)
    (family : Finset Tuple) (E beta : K[X]) (sparseSource bad : Finset K)
    (sameBad : bad = SelectedMiddleImageRecovery.Generic.exceptionSet family
      (Gamma.filter fun gamma => beta.eval gamma=0) (sparseSource ∩ Gamma)
      (insufficientHits e.c1 e.c2 Gamma))
    (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1)
    (cover : CandidateClassifies e.c1 e.c2 Gamma family E beta sparseSource e.data)
    (outsidePair : ¬PairRoot E e.data) (gamma kappa tau alpha : K)
    (inside : gamma ∈ Gamma) (outsideBad : gamma ∉ bad)
    (high : HighPrefix e gamma kappa tau alpha) :
    RecoveredHigh e family gamma kappa tau alpha := by
  obtain ⟨Q, witness, image, _rows, enough⟩ :=
    SelectedAcceptedPrefixPartition.high_same_quotient e gamma kappa tau alpha high
  have close := high_support_of_fibre_count (e.raw gamma) Q enough
  have nonexception : gamma ∉ SelectedMiddleImageRecovery.Generic.exceptionSet family
      (Gamma.filter fun value => beta.eval value=0) (sparseSource ∩ Gamma)
      (insufficientHits e.c1 e.c2 Gamma) := by
    rw [← sameBad]
    exact outsideBad
  have outcome := candidate_outcome e.c1 e.c2 Gamma family E beta sparseSource
    e.data checked circles west cover gamma inside Q image enough
  have recovered : Recovered e.c1 e.c2 family e.data gamma Q :=
    Generic.outcome_recovered outcome outsidePair nonexception
  exact ⟨Q, witness, close, recovered⟩

/-- A counterexample to recovery can occur only at an exceptional gamma.
This inclusion does not use the eventual query or terminal acceptance. -/
theorem residual_high_mem {q : Nat} (e : Execution q) (family : Finset Tuple)
    (bad : Finset K) (gamma kappa tau alpha : K)
    (recover : gamma ∉ bad → HighPrefix e gamma kappa tau alpha →
      RecoveredHigh e family gamma kappa tau alpha)
    (residual : HighPrefix e gamma kappa tau alpha ∧
      ¬RecoveredHigh e family gamma kappa tau alpha) : gamma ∈ bad := by
  by_contra outside
  exact residual.2 (recover outside residual.1)

def highResidualSlice {q : Nat} (e : Execution q) (family : Finset Tuple)
    (gamma : K) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if HighPrefix e gamma kappa tau alpha ∧ ¬RecoveredHigh e family gamma kappa tau alpha
    then suffix e gamma kappa tau alpha A G else 0)))

/-- Definitionally the high-residual mean used by the separate composition
leaf, with its recovered predicate specialized to RecoveredHigh. -/
def highResidualProbability {q : Nat} (e : Execution q) (family : Finset Tuple)
    (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => highResidualSlice e family gamma A G)

/-- Retain the actual suffix; replace it by one only on the exceptional
event. The final remains the same strategy output after tau/alpha. -/
theorem high_residual_indicator {q : Nat} (e : Execution q) (family : Finset Tuple)
    (bad : Finset K) (gamma kappa tau alpha : K)
    (recover : gamma ∉ bad → HighPrefix e gamma kappa tau alpha →
      RecoveredHigh e family gamma kappa tau alpha)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (count : q ≤ 262144) :
    (if HighPrefix e gamma kappa tau alpha ∧ ¬RecoveredHigh e family gamma kappa tau alpha
      then suffix e gamma kappa tau alpha A G else 0) ≤
      if gamma ∈ bad then (1 : ℚ) else 0 := by
  by_cases residual : HighPrefix e gamma kappa tau alpha ∧
      ¬RecoveredHigh e family gamma kappa tau alpha
  · have hit := residual_high_mem e family bad gamma kappa tau alpha recover residual
    rw [if_pos residual, if_pos hit]
    exact after_unit ((e.rows gamma).before kappa) e.quarterChecked
      (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha A G ha hg
      (by rwa [domain_card])
  · rw [if_neg residual]
    split_ifs <;> norm_num

/-- Separate the finite-mean consumer from the selected classification.
One fixed bad set must work across all later kappa/tau/alpha histories. -/
theorem high_residual_card_bound {q : Nat} (e : Execution q) (family : Finset Tuple)
    (bad : Finset K) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (count : q ≤ 262144)
    (recover : ∀ gamma ∈ Gamma, ∀ kappa tau alpha,
      gamma ∉ bad → HighPrefix e gamma kappa tau alpha →
        RecoveredHigh e family gamma kappa tau alpha) :
    highResidualProbability e family A G Gamma ≤ (bad.card : ℚ)/Gamma.card := by
  apply Generic.mean_indicator_card Gamma bad (fun gamma => highResidualSlice e family gamma A G)
  intro gamma inside
  apply avg_le G hg
  intro kappa _
  apply avg_le G hg
  intro tau _
  apply avg_le A ha
  intro alpha _
  exact high_residual_indicator e family bad gamma kappa tau alpha
    (recover gamma inside kappa tau alpha) A G ha hg count

/-- The source-shaped high residual bound, outside the supplied SAME
pre-OOD obstruction. Prefix existence stays external; no pair sampler, FS,
earlyC1 success or new repair term is imported. Gamma is not conditioned
on nonexceptional values, and its empty-set convention remains valid. -/
theorem high_residual_probability_bound {q : Nat} (e : Execution q)
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
    (outsidePair : ¬PairRoot E e.data) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (count : q ≤ 262144) :
    highResidualProbability e family A G Gamma ≤ (104 : ℚ)/Gamma.card := by
  have bounded := high_residual_card_bound e family bad A G Gamma ha hg count
    (fun gamma inside kappa tau alpha outsideBad high =>
      high_recovered e Gamma family E beta sparseSource bad sameBad checked circles west
        cover outsidePair gamma kappa tau alpha inside outsideBad high)
  have small : bad.card ≤ 104 := by
    rw [sameBad]
    exact selected_exception_card e.c1 e.c2 Gamma family one beta betaNonzero
      betaDegree sparseSource sparseSmall
  have rational : (bad.card : ℚ) ≤ 104 := Nat.cast_le.mpr small
  exact bounded.trans (div_le_div_of_nonneg_right rational (Nat.cast_nonneg _))

#print axioms Generic.outcome_recovered
#print axioms Generic.mean_indicator_card
#print axioms recovered_high_implies_high
#print axioms high_support_of_fibre_count
#print axioms high_recovered
#print axioms residual_high_mem
#print axioms high_residual_indicator
#print axioms high_residual_card_bound
#print axioms high_residual_probability_bound
end
end AspisV8.SelectedResidualHighRecovery
