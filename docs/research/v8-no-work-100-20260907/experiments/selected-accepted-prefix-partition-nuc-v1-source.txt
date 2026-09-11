import SelectedMiddleGammaCover

/-! Deterministic partition of the EXISTING selected ideal compact-field
acceptance predicate. This does not translate verify_parsed, authenticate a
total received word, or manufacture a Rust-to-Execution correspondence.
No probability, gamma cardinality, later repair, or FS theorem is replayed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedAcceptedPrefixPartition

inductive Branch where
  | noGood | noFactor | lower | low | high
  deriving DecidableEq

def Branch.holds (good factor higher high : Prop) : Branch → Prop
  | .noGood => ¬good
  | .noFactor => good ∧ ¬factor
  | .lower => factor ∧ ¬higher
  | .low => higher ∧ ¬high
  | .high => high

/-- Exact mutually exclusive precedence; an existential low witness cannot
be substituted for the complement of the existential high event. -/
theorem unique_branch (good factor higher high : Prop)
    (factorGood : factor → good) (higherFactor : higher → factor)
    (highHigher : high → higher) :
    ∃! branch, branch.holds good factor higher high := by
  classical
  have disjoint (i j : Branch) (different : i ≠ j)
      (left : i.holds good factor higher high) :
      ¬j.holds good factor higher high := by
    cases i <;> cases j <;> simp_all [Branch.holds]
  have existsBranch : ∃ branch, branch.holds good factor higher high := by
    by_cases g : good
    · by_cases f : factor
      · by_cases h : higher
        · by_cases s : high
          · exact ⟨.high, s⟩
          · exact ⟨.low, h, s⟩
        · exact ⟨.lower, f, h⟩
      · exact ⟨.noFactor, g, f⟩
    · exact ⟨.noGood, g⟩
  obtain ⟨branch, present⟩ := existsBranch
  refine ⟨branch, present, ?_⟩
  intro other otherPresent
  by_contra different
  exact disjoint other branch different otherPresent present

open Polynomial Finset
open AspisV8.CausalCoveredRecovery AspisV8.CausalFactorReduction
open AspisV8.SelectedHigherYBranch AspisV8.SelectedHigherYHighSupport
open AspisV8.SelectedCoveredRelation AspisV8.CausalOrderedRelation
open AspisV8.SelectedReceivedOracle AspisV8.QuotientFamilySelected
open AspisV8.GammaComponentGame AspisV8.OODInterpolant
open AspisV8.OffFamilyIntersection AspisV8.SelectedRegularLowSupport
open AspisV8.ReferenceIndependentRelation AspisV8.SelectedQuadraticReduction
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- This is the already constructed compact-field accept predicate, NOT a
new definition claiming that the Rust verifier returned Ok. -/
def idealAccepts {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (queries : OrderedQueryGame.Schedule domain q) (rho : K) (later : List K) : Prop :=
  CausalOrderedRelation.accepts ((e.rows gamma).before kappa)
    (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha queries rho later

def prefixCase {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (branch : Branch) : Prop :=
  branch.holds (goodPrefix e gamma kappa tau alpha)
    (factorPrefix e gamma kappa tau alpha) (higherPrefix e gamma kappa tau alpha)
    (HighPrefix e gamma kappa tau alpha)

theorem higher_implies_factor {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (higher : higherPrefix e gamma kappa tau alpha) :
    factorPrefix e gamma kappa tau alpha := by
  obtain ⟨Q, member, notBad, final, F, factor, retained, root, _⟩ := higher
  exact ⟨Q, member, notBad, final, F, factor, retained, root⟩

/-- Every accepted ideal run belongs to exactly one branch. No accepted
branch is thrown away, and Q/final selection has not moved before alpha. -/
theorem accepted_partition {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (queries : OrderedQueryGame.Schedule domain q) (rho : K) (later : List K) :
    idealAccepts e gamma kappa tau alpha queries rho later ↔
      ∃! branch, idealAccepts e gamma kappa tau alpha queries rho later ∧
        prefixCase e gamma kappa tau alpha branch := by
  constructor
  · intro accepted
    obtain ⟨branch, present, unique⟩ := unique_branch
      (goodPrefix e gamma kappa tau alpha) (factorPrefix e gamma kappa tau alpha)
      (higherPrefix e gamma kappa tau alpha) (HighPrefix e gamma kappa tau alpha)
      (factor_implies_good e gamma kappa tau alpha)
      (higher_implies_factor e gamma kappa tau alpha)
      (high_prefix_higher e gamma kappa tau alpha)
    exact ⟨branch, ⟨accepted, present⟩, fun other h => unique other h.2⟩
  · rintro ⟨branch, present, _⟩
    exact present.1

/-- A missing good representative cannot simply be relabeled high. Its
off-family, nonzero-prior and early-collision alternatives remain explicit.
Acceptance is immaterial to this pointwise first-response implication. -/
theorem no_good_cases {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (missing : ¬goodPrefix e gamma kappa tau alpha) :
    SelectedOutsideQuery.outside (e.raw gamma) alpha ((e.strategy gamma kappa).final tau alpha) ∨
      (atFold ((e.rows gamma).before kappa) (e.strategy gamma kappa) tau alpha).prior
        ((e.strategy gamma kappa).final tau alpha) ≠ 0 ∨
      ∃ Q ∈ badFamily (e.rows gamma) (e.raw gamma),
        firstCollision (e.rows gamma) (e.strategy gamma) Q kappa tau alpha := by
  classical
  by_cases outside : SelectedOutsideQuery.outside (e.raw gamma) alpha
      ((e.strategy gamma kappa).final tau alpha)
  · exact Or.inl outside
  · by_cases prior : (atFold ((e.rows gamma).before kappa)
        (e.strategy gamma kappa) tau alpha).prior ((e.strategy gamma kappa).final tau alpha)=0
    · have represented : CoveredAt univ (e.raw gamma) 9558 alpha
          ((e.strategy gamma kappa).final tau alpha) := Classical.not_not.mp outside
      obtain ⟨Q, member, final⟩ := represented
      have inFamily := (mem_literalFamily (e.raw gamma) Q).mpr member
      have bad : badAnchor (e.rows gamma) Q := by
        by_contra notBad
        exact missing ⟨Q, inFamily, notBad, final⟩
      have collision : firstCollision (e.rows gamma) (e.strategy gamma) Q kappa tau alpha := by
        rw [final, SelectedCoveredRelation.prior_at_fold] at prior
        exact prior
      exact Or.inr (Or.inr ⟨Q, Finset.mem_filter.mpr ⟨inFamily, bad⟩, collision⟩)
    · exact Or.inr (Or.inl prior)

/-- The high branch exposes all classifier inputs for ONE actual witness:
image equations, all four original row errors zero, the actual final,
literal family membership, original higher factor root and exact support.
The support is derived from HighSupport, never from terminal acceptance. -/
theorem high_same_quotient {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (high : HighPrefix e gamma kappa tau alpha) :
    ∃ Q, Witness e gamma kappa tau alpha Q ∧
      (Q 1023=0 ∧ e.data.b*Q 1022-e.data.c*Q 1021=0) ∧
      (replaceRows (e.rows gamma) Q).errors=0 ∧
      200808 ≤ fibreCount (e.raw gamma) Q := by
  obtain ⟨Q, witness, close⟩ := high
  have image := witness_image e gamma kappa tau alpha Q witness
  have rows : (replaceRows (e.rows gamma) Q).errors=0 := by
    by_contra wrong
    exact witness.2.1 (Or.inr (Or.inr wrong))
  have partition := SelectedMiddleGammaCover.full_bad_partition (e.raw gamma) Q
  change (PartialFoldRecovery.fibreBad
    (AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder Q) (e.raw gamma)).card ≤ 4*15334 at close
  exact ⟨Q, witness, image, rows, by omega⟩

#print axioms unique_branch
#print axioms higher_implies_factor
#print axioms accepted_partition
#print axioms no_good_cases
#print axioms high_same_quotient
end
end AspisV8.SelectedAcceptedPrefixPartition
