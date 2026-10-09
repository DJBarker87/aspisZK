import SelectedCompactSemanticRepairV4
import SelectedSemanticLaneAggregationV2

/-! Causal degree-27 repair mass and the selected semantic-terminal split.
This narrowly ports the finite-mean induction from V7's
V5AdaptiveSumcheckChallengeBound/V5FiatShamirAdaptiveQueryBudget. It uses
the actual compact recurrence, never the old full-message source framing.
The ideal challenge mean is explicit and is not a SHA/ROM theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedSemanticTerminalAlternative
open scoped BigOperators
open Polynomial Finset
open AspisV8.JointImageGame AspisV8.SelectedCompactSemanticRepair
open AspisV8.SelectedSemanticLaneAggregation AspisV8.SelectedSemanticHelperAggregation
open AspisV6TranscriptRelationGrammar AspisV6AcceptedPathObligations
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

/-- The two messages are functions of preceding answers only. All prefix
data, including adaptive C2 and eta, may be captured by the fixed plan. -/
structure Plan (K : Type*) [Field K] where
  claimed : List K → K[X]
  reference : List K → K[X]
  claimedDegree : ∀ history, (claimed history).natDegree ≤ 27
  referenceDegree : ∀ history, (reference history).natDegree ≤ 27

def Plan.bad (plan : Plan K) (S : Finset K) (history : List K) : Finset K :=
  badRound S (plan.claimed history) (plan.reference history)

theorem Plan.bad_card (plan : Plan K) (S : Finset K) (history : List K) :
    (plan.bad S history).card ≤ 27 :=
  badRound_card S _ _ (plan.claimedDegree history) (plan.referenceDegree history)

theorem Plan.bad_subset (plan : Plan K) (S : Finset K) (history : List K) :
    plan.bad S history ⊆ S := by
  classical
  unfold Plan.bad badRound
  split_ifs
  · exact Finset.empty_subset _
  · exact Finset.filter_subset _ _

/-- Exact fresh-answer tree mean: a hit pays 1 and ends the charged event;
otherwise the next bad set uses the extended history. No independence of
the adaptively selected bad sets is assumed. -/
def failure (S : Finset K) (plan : Plan K) : Nat → List K → ℚ
  | 0, _ => 0
  | n+1, history => avg S (fun answer =>
      if answer∈plan.bad S history then 1 else failure S plan n (history++[answer]))

theorem failure_unit (S : Finset K) (nonempty : S.Nonempty) (plan : Plan K)
    (n : Nat) (history : List K) : 0 ≤ failure S plan n history ∧ failure S plan n history ≤ 1 := by
  induction n generalizing history with
  | zero => simp [failure]
  | succ n ih =>
    constructor
    · apply avg_nonneg
      intro answer _
      split_ifs
      · norm_num
      · exact (ih (history++[answer])).1
    · apply avg_le S nonempty
      intro answer _
      split_ifs
      · exact le_refl 1
      · exact (ih (history++[answer])).2

theorem failure_bound (S : Finset K) (nonempty : S.Nonempty) (plan : Plan K)
    (n : Nat) (history : List K) :
    failure S plan n history ≤ (n : ℚ)*27/S.card := by
  induction n generalizing history with
  | zero => simp [failure]
  | succ n ih =>
    have step := avg_exception S (plan.bad S history) nonempty
      (plan.bad_subset S history)
      (fun answer => if answer∈plan.bad S history then 1
        else failure S plan n (history++[answer]))
      ((n : ℚ)*27/S.card) (by positivity)
      (by
        intro answer _
        split_ifs
        · exact le_refl 1
        · exact (failure_unit S nonempty plan n (history++[answer])).2)
      (by
        intro answer _ outside
        simpa only [if_neg outside] using ih (history++[answer]))
    have count : ((plan.bad S history).card : ℚ)/S.card ≤ (27 : ℚ)/S.card :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr (plan.bad_card S history)) (Nat.cast_nonneg _)
    calc
      failure S plan (n+1) history ≤
          ((plan.bad S history).card : ℚ)/S.card+(n : ℚ)*27/S.card := step
      _ ≤ (27 : ℚ)/S.card+(n : ℚ)*27/S.card := add_le_add_right count _
      _ = ((n+1 : Nat) : ℚ)*27/S.card := by push_cast; ring

theorem ten_round_bound (S : Finset K) (nonempty : S.Nonempty) (plan : Plan K) :
    failure S plan 10 [] ≤ (270 : ℚ)/S.card := by
  simpa using failure_bound S nonempty plan 10 []

def historyBefore (point : Fin 10 → K) (round : Fin 10) : List K :=
  List.ofFn fun previous : Fin round.val => point ⟨previous.val, lt_trans previous.isLt round.isLt⟩

/-- This source-to-plan obligation is not inferred from the final transcript.
In particular a reference record alone does not discharge it. -/
structure FollowsPlan (fields : FixedFieldView K) (point : Fin 10 → K)
    {table : Fin 1024 → K} (reference : ReferenceTrace table point) (plan : Plan K) : Prop where
  claimed : ∀ round, plan.claimed (historyBefore point round)=compactPolynomial fields point round
  reference : ∀ round, plan.reference (historyBefore point round)=reference.messages round

def RepairHit (S : Finset K) (plan : Plan K) (point : Fin 10 → K) : Prop :=
  ∃ round, point round∈plan.bad S (historyBefore point round)

theorem repair_hits_plan (S : Finset K) (fields : FixedFieldView K) (point : Fin 10 → K)
    {table : Fin 1024 → K} (reference : ReferenceTrace table point) (plan : Plan K)
    (causal : FollowsPlan fields point reference plan) (inside : ∀ round, point round∈S)
    (repair : ∃ round, Repair fields point reference round) : RepairHit S plan point := by
  obtain ⟨round, repaired⟩ := repair
  refine ⟨round, ?_⟩
  unfold Plan.bad
  rw [causal.claimed, causal.reference]
  exact repair_hits_badRound S fields point reference round (inside round) repaired

theorem map_alternatives {A B C D E F : Prop} (h : A ∨ B ∨ C ∨ D)
    (left : A → E) (right : D → F) : E ∨ B ∨ C ∨ F := by
  rcases h with a | b | c | d
  · exact Or.inl (left a)
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (right d)))

/-- Generic reference-table boundary, kept opaque before source specialization. -/
theorem compact_alternative (S : Finset K) (fields : FixedFieldView K) (point : Fin 10 → K)
    (eta : K) (etaNonzero : eta≠0) (real mask : Fin 1024 → K)
    (reference : ReferenceTrace (maskedTable eta real mask) point) (plan : Plan K)
    (causal : FollowsPlan fields point reference plan) (inside : ∀ round, point round∈S)
    (Outcome : Prop) (unmasked : (∑ row, real row)=0 → Outcome) :
    Outcome ∨ fields.initialClaim≠(∑ row, mask row) ∨
    semanticTerminalClaim fields point≠
      referenceClaim (∑ row, maskedTable eta real mask row) reference.messages point (Fin.last 10) ∨
    RepairHit S plan point :=
  map_alternatives (compact_unmasked_or_failures fields point eta etaNonzero real mask reference)
    unmasked (repair_hits_plan S fields point reference plan causal inside)

def realTable (lanes : Fin 1024 → RowLanes K) (helper active : Fin 1024 → K)
    (theta : K) (equalityPoint : Fin 10 → K) (mu : K) : Fin 1024 → K :=
  unmaskedTable (mleRowWeight equalityPoint) (thetaTable lanes theta) helper active mu

section Finite
variable [Fintype K]

def AlgebraicOutcome (T M : Finset K) (lanes : Fin 1024 → RowLanes K)
    (helper active : Fin 1024 → K) (theta : K) (equalityPoint : Fin 10 → K) (mu : K) : Prop :=
  (AllRowsZero lanes ∧ (∑ row, helper row)=0 ∧ (∑ row, (1-active row)*helper row)=0) ∨
  theta∈badTheta T lanes ∨ equalityPoint∈badPoint (thetaTable lanes theta) ∨
  mu∈badMu M (tableMLEValue equalityPoint (thetaTable lanes theta))
    (∑ row, helper row) (∑ row, (1-active row)*helper row)

/-- Total selected29/ten-coordinate/quadratic-helper alternative through the
literal ten-round compact recurrence. The two authentication failures remain
unbounded named alternatives; the ideal plan count is a separate theorem.
No accepted opening is silently replaced by its fixed-table evaluation. -/
theorem selected_terminal_alternative (T M S : Finset K)
    (fields : FixedFieldView K) (point : Fin 10 → K)
    (lanes : Fin 1024 → RowLanes K) (helper active mask : Fin 1024 → K)
    (theta : K) (equalityPoint : Fin 10 → K) (mu eta : K)
    (thetaInside : theta∈T) (muInside : mu∈M) (etaNonzero : eta≠0)
    (reference : ReferenceTrace
      (maskedTable eta (realTable lanes helper active theta equalityPoint mu) mask) point)
    (plan : Plan K) (causal : FollowsPlan fields point reference plan)
    (inside : ∀ round, point round∈S) :
    AlgebraicOutcome T M lanes helper active theta equalityPoint mu ∨
    fields.initialClaim≠(∑ row, mask row) ∨
    semanticTerminalClaim fields point≠
      referenceClaim
        (∑ row, maskedTable eta (realTable lanes helper active theta equalityPoint mu) mask row)
        reference.messages point (Fin.last 10) ∨
    RepairHit S plan point := by
  apply compact_alternative S fields point eta etaNonzero
    (realTable lanes helper active theta equalityPoint mu) mask reference plan causal inside
  intro zero
  exact source_zero_alternative T M lanes helper active theta equalityPoint mu
    thetaInside muInside zero

end Finite

#print axioms Plan.bad_card
#print axioms failure_unit
#print axioms ten_round_bound
#print axioms repair_hits_plan
#print axioms compact_alternative
#print axioms selected_terminal_alternative
end
end AspisV8.SelectedSemanticTerminalAlternative
