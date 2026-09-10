import CausalHigherYClassification
import SelectedOriginalInjectivity
import FoldSupportClosure

/-! Source-review draft. Fix the received/OOD prefix, factor, regular row and
gamma. Uniqueness identifies every qualifying post-alpha final with the fold
of one Q; it does not make Q polynomial in gamma. Actual ordered query
residuals are then retained. A schedule containing a non-full Q fibre has at
most three matching alphas, not zero. The compact suffix contributes only
the existing shifted-query and later-round repair terms, once.
No probability product, authentication or Fiat--Shamir coupling is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedRegularQueryBridge
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisV8.SelectedReceivedOracle AspisV8.SelectedHigherYBranch
open AspisV8.SelectedOODGate AspisV8.CausalCoveredRecovery
open AspisV8.ComponentOODBinding
open AspisV8.CausalHigherYClassification AspisV8.CausalOrderedRelation
open AspisV8.RelationCompatibleMoment AspisV8.JointImageGame
open AspisV8.OrderedQueryGame AspisV8.FoldSupportClosure
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- One actual regular witness identifies every final on this branch,
including witnesses chosen at different kappa/tau/alpha histories. -/
theorem fixed_regular_final {q : Nat} (e : Execution q)
    (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (F : TrivariatePolynomial K)
    (r : Fin 2) (gamma : K) (Q : Fin 1024 → K)
    (qualified : Qualified e.c1 e.c2 e.data F gamma Q)
    (kappa tau alpha : K)
    (selected : fixedRegularPrefix e F r gamma kappa tau alpha) :
    (e.strategy gamma kappa).final tau alpha=coefficientFoldLayer 256 alpha Q := by
  obtain ⟨Q', qualified', _, final, regular⟩ := selected
  have same := SelectedOriginalInjectivity.regular_qualified_unique
    e.c1 e.c2 e.data checked circles west F gamma Q' Q qualified' qualified r regular
  exact final.trans (congrArg (coefficientFoldLayer 256 alpha) same)

/-- The quotient is constructed before quantifying over later histories.
Existence of one regular prefix suffices; no selected-Q premise is retained
at this endpoint. This says nothing about uniform dependence on gamma. -/
theorem exists_fixed_regular_final {q : Nat} (e : Execution q)
    (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (F : TrivariatePolynomial K)
    (r : Fin 2) (gamma : K)
    (present : ∃ kappa tau alpha, fixedRegularPrefix e F r gamma kappa tau alpha) :
    ∃ Q, Qualified e.c1 e.c2 e.data F gamma Q ∧
      ∀ kappa tau alpha, fixedRegularPrefix e F r gamma kappa tau alpha →
        (e.strategy gamma kappa).final tau alpha=coefficientFoldLayer 256 alpha Q := by
  obtain ⟨kappa, tau, alpha, Q, qualified, _⟩ := present
  exact ⟨Q, qualified, fun kappa tau alpha selected =>
    fixed_regular_final e checked circles west F r gamma Q qualified
      kappa tau alpha selected⟩

/-- Actual field-domain ordered schedules transport to the very same
indexed fibre checks. No reordering or independent query sample is used. -/
theorem actual_query_matches_iff {q : Nat}
    (received : Fin 1048576 → K) (final : Fin 256 → K) (alpha : K)
    (queries : Schedule domain q) :
    PostQueryFunctional.residual final (fun j => (queries j : K))
      ((oracle 0 received).folded alpha)=0 ↔
    ∀ j, Matches received alpha final (index (queries j : K)) := by
  constructor
  · intro zero j
    have actualValue := congrFun zero j
    simp only [PostQueryFunctional.residual, Pi.zero_apply] at actualValue
    have coordinate := point_index (queries j : K) (queries j).property
    rw [← coordinate, final_evaluation, oracle_folded] at actualValue
    change exactFinalLinear final (index (queries j : K)) =
      circleFoldLayer 262144 alpha (canonicalOneFoldSchedule 0).circleInv2x
        (canonicalOneFoldSchedule 0).circleInv2y received (index (queries j : K))
    exact sub_eq_zero.mp actualValue
  · intro matching
    funext j
    simp only [PostQueryFunctional.residual, Pi.zero_apply]
    have coordinate := point_index (queries j : K) (queries j).property
    rw [← coordinate, final_evaluation, oracle_folded]
    change exactFinalLinear final (index (queries j : K)) -
      circleFoldLayer 262144 alpha (canonicalOneFoldSchedule 0).circleInv2x
        (canonicalOneFoldSchedule 0).circleInv2y received (index (queries j : K)) = 0
    exact sub_eq_zero.mpr (matching j)

/-- A single bad queried fibre controls all matched alphas. Four matches
would recover its raw slots, by the already checked cubic fold theorem. -/
theorem nonfull_schedule_alphas_le_three {q : Nat}
    (received : Fin 1048576 → K) (Q : Fin 1024 → K) (A : Finset K)
    (queries : Fin q → Fin 262144)
    (bad : ∃ j, ¬FullSlots received Q (queries j)) :
    (A.filter fun alpha => ∀ j,
      Matches received alpha (coefficientFoldLayer 256 alpha Q) (queries j)).card ≤ 3 := by
  obtain ⟨j, bad⟩ := bad
  by_contra larger
  have four : 4 ≤ (matchingNodes received A
      (fun alpha => coefficientFoldLayer 256 alpha Q) (queries j)).card := by
    have included : (A.filter fun alpha => ∀ j,
        Matches received alpha (coefficientFoldLayer 256 alpha Q) (queries j)) ⊆
        matchingNodes received A (fun alpha => coefficientFoldLayer 256 alpha Q)
          (queries j) := by
      intro alpha member
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp member).1, (Finset.mem_filter.mp member).2 j⟩
    have size := Finset.card_le_card included
    omega
  exact bad (four_identified_matches received Q A
    (fun alpha => coefficientFoldLayer 256 alpha Q) (fun _ _ => rfl) (queries j) four)

/-- The adaptive strategy remains inside the counted event. No final is
frozen before alpha: regular uniqueness is applied only when the actual
prefix qualifies. Residual-zero is not inferred from terminal acceptance. -/
theorem regular_nonfull_schedule_alphas_le_three {q : Nat} (e : Execution q)
    (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (F : TrivariatePolynomial K)
    (r : Fin 2) (gamma : K) (Q : Fin 1024 → K)
    (qualified : Qualified e.c1 e.c2 e.data F gamma Q)
    (kappa tau : K) (A : Finset K) (queries : Schedule domain q)
    (bad : ∃ j, ¬FullSlots (e.raw gamma) Q (index (queries j : K))) :
    (A.filter fun alpha => fixedRegularPrefix e F r gamma kappa tau alpha ∧
      PostQueryFunctional.residual ((e.strategy gamma kappa).final tau alpha)
        (fun j => (queries j : K)) ((oracle 0 (e.raw gamma)).folded alpha)=0).card ≤ 3 := by
  apply (Finset.card_le_card ?_).trans
    (nonfull_schedule_alphas_le_three (e.raw gamma) Q A
      (fun j => index (queries j : K)) bad)
  intro alpha member
  obtain ⟨inA, selected, residualZero⟩ := Finset.mem_filter.mp member
  have matched := (actual_query_matches_iff (e.raw gamma)
    ((e.strategy gamma kappa).final tau alpha) alpha queries).mp residualZero
  rw [fixed_regular_final e checked circles west F r gamma Q qualified
    kappa tau alpha selected] at matched
  exact Finset.mem_filter.mpr ⟨inA, matched⟩

/-- Export the matching-only inequality so a union of regular factors can
be counted AFTER one global suffix reduction. Summing per-factor scalar
repair bounds is neither required nor licensed by this interface. -/
theorem regular_matching_moment_bound {q : Nat} (e : Execution q)
    (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (F : TrivariatePolynomial K)
    (r : Fin 2) (gamma : K) (Q : Fin 1024 → K)
    (qualified : Qualified e.c1 e.c2 e.data F gamma Q) (kappa tau alpha : K)
    (selected : fixedRegularPrefix e F r gamma kappa tau alpha) :
    compatibleMoment (atFold ((e.rows gamma).before kappa)
      (e.strategy gamma kappa) tau alpha) ((e.strategy gamma kappa).final tau alpha)
      ((oracle 0 (e.raw gamma)).folded alpha) domain q ≤
    matchingRatio domain q (coefficientFoldLayer 256 alpha Q)
      ((oracle 0 (e.raw gamma)).folded alpha) := by
  rw [fixed_regular_final e checked circles west F r gamma Q qualified
    kappa tau alpha selected]
  unfold compatibleMoment
  split_ifs
  · exact le_refl _
  · unfold matchingRatio
    positivity

/-- Actual compact-suffix acceptance on this regular branch is bounded by
the fixed-Q JOINT alpha/query matching moment, not a product of marginals.
The matching moment still contains cubic alpha roots outside full support.
Only rho and the three later repairs are charged here; no 6/|A| first-stage
charge, factor-family multiplier, or extra query union is introduced. -/
theorem fixed_regular_suffix_bound {q : Nat} (e : Execution q)
    (checked : e.data.Checked)
    (circles : e.data.x0^2+e.data.y0^2=1 ∧ e.data.x1^2+e.data.y1^2=1)
    (west : ∀ r, pointX e.data r ≠ -1) (F : TrivariatePolynomial K)
    (r : Fin 2) (gamma : K) (Q : Fin 1024 → K)
    (qualified : Qualified e.c1 e.c2 e.data F gamma Q) (kappa : K)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (positive : 0<q) (count : q≤262144) :
    avg G (fun tau => avg A (fun alpha =>
      if fixedRegularPrefix e F r gamma kappa tau alpha then
        suffix e gamma kappa tau alpha A G else 0)) ≤
      avg A (fun alpha => matchingRatio domain q (coefficientFoldLayer 256 alpha Q)
        ((oracle 0 (e.raw gamma)).folded alpha))+(q:ℚ)/G.card+18/A.card := by
  have countDomain : q≤domain.card := by simpa only [domain_card] using count
  have bound := causal_supported_bound ((e.rows gamma).before kappa) e.quarterChecked
    (oracle 0 (e.raw gamma)) (e.strategy gamma kappa)
    (fixedRegularPrefix e F r gamma kappa) A G ha hg positive countDomain
  have pointwise (tau alpha : K) :
      (if fixedRegularPrefix e F r gamma kappa tau alpha then
        compatibleMoment (atFold ((e.rows gamma).before kappa)
          (e.strategy gamma kappa) tau alpha) ((e.strategy gamma kappa).final tau alpha)
          ((oracle 0 (e.raw gamma)).folded alpha) domain q else 0) ≤
      matchingRatio domain q (coefficientFoldLayer 256 alpha Q)
        ((oracle 0 (e.raw gamma)).folded alpha) := by
    have nonnegative : 0 ≤ matchingRatio domain q (coefficientFoldLayer 256 alpha Q)
        ((oracle 0 (e.raw gamma)).folded alpha) := by
      unfold matchingRatio
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    by_cases selected : fixedRegularPrefix e F r gamma kappa tau alpha
    · rw [if_pos selected]
      exact regular_matching_moment_bound e checked circles west F r gamma Q qualified
        kappa tau alpha selected
    · simpa only [if_neg selected] using nonnegative
  have moments := avg_mono G _ _ (fun tau _ =>
    avg_mono A _ _ (fun alpha _ => pointwise tau alpha))
  rw [avg_constant G hg] at moments
  exact bound.trans (add_le_add (add_le_add moments (le_refl _)) (le_refl _))

#print axioms fixed_regular_final
#print axioms exists_fixed_regular_final
#print axioms actual_query_matches_iff
#print axioms nonfull_schedule_alphas_le_three
#print axioms regular_nonfull_schedule_alphas_le_three
#print axioms regular_matching_moment_bound
#print axioms fixed_regular_suffix_bound
end
end AspisV8.SelectedRegularQueryBridge
