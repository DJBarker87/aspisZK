import PreImageAnchorSelected
import SelectedReceivedOracle
import RepresentedImageGame
import ReferenceIndependentRelation
import PreAnchorEligibility

/-! Joint selected geometry and causal image/row relation accounting.
The same fixed arbitrary indexed quotient supplies both geometry and queries.
The reference is chosen from that geometry before kappa/tau; replacing it
does not change the executed field grammar. Far finals and correct-row
anchors are retained as unbounded residual classes, not extraction failures
silently removed by a provider. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 400000
namespace AspisV8.PreAnchorJoint
open Finset
open AspisV5ComponentCQM31TowerExact AspisV5FriConcreteEncoderCommutation
open AspisV5ComponentCConcreteFoldLinearity
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV8.PartialFoldRecovery AspisV8.PartialFoldSelected
open AspisV8.PreImageAnchorSelected AspisV8.SelectedReceivedOracle
open AspisV8.CausalOrderedRelation AspisV8.FirstImageDiscrepancy
open AspisV8.PostQueryFunctional AspisV8.ShiftedRowPrefix
open AspisV8.JointImageGame AspisV8.RepresentedImageGame
open AspisV8.ReferenceIndependentRelation
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def near {q : Nat} (received : Fin 1048576 → K) (B : Nat)
    (strategy : K → Strategy domain q) (kappa tau alpha : K) : Prop :=
  (foldedBad exactFinalLinear (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y received alpha
    ((strategy kappa).final tau alpha)).card ≤ B

def badReference (rows : Rows (K := K)) : Prop :=
  rows.referenceQ ⟨1023, by decide⟩≠0 ∨
  rows.b*rows.referenceQ ⟨1022, by decide⟩-
    rows.c*rows.referenceQ ⟨1021, by decide⟩≠0 ∨ rows.errors≠0

/-- Sparse geometry bounds every causal continuation on this event, not
merely an honestly chosen final. Queries, rho and all tails are retained. -/
theorem sparse_near_bound {q : Nat} (received : Fin 1048576 → K) (B : Nat)
    (rows : Rows (K := K)) (hq : rows.quarter*4=1)
    (strategy : K → Strategy domain q) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hcount : q≤domain.card)
    (sparse : (selectedCloseChallenges received B A).card≤3) :
    supportedRowsProbability rows hq (oracle rows.referenceQ received)
      strategy (near received B strategy) A G ≤ 3/A.card := by
  classical
  apply avg_le G hg
  intro kappa _
  apply avg_le G hg
  intro tau _
  have contained : selectedCloseChallenges received B A⊆A :=
    PreAnchorEligibility.eligible_subset exactFinalLinear
      (canonicalOneFoldSchedule 0).circleInv2x (canonicalOneFoldSchedule 0).circleInv2y
      received B A
  have h := avg_exception A (selectedCloseChallenges received B A) ha
    contained (fun alpha =>
      if near received B strategy kappa tau alpha then
        (after (rows.before kappa) hq (oracle rows.referenceQ received)
          (strategy kappa) tau alpha).prob A G else 0) 0 (by norm_num)
    (by
      intro alpha _
      split_ifs
      · exact after_unit (rows.before kappa) hq (oracle rows.referenceQ received)
          (strategy kappa) tau alpha A G ha hg hcount
      · norm_num)
    (by
      intro alpha halpha outside
      have notNear : ¬near received B strategy kappa tau alpha := by
        intro close
        apply outside
        exact PreAnchorEligibility.eligible_mem exactFinalLinear
          (canonicalOneFoldSchedule 0).circleInv2x (canonicalOneFoldSchedule 0).circleInv2y
          received B A alpha halpha ((strategy kappa).final tau alpha) close
      simp only [if_neg notNear, le_refl])
  have hc : ((selectedCloseChallenges received B A).card:ℚ)≤3 := by exact_mod_cast sparse
  have h' : (by classical exact avg A (fun alpha =>
      if near received B strategy kappa tau alpha then
        (after (rows.before kappa) hq (oracle rows.referenceQ received)
          (strategy kappa) tau alpha).prob A G else 0)) ≤
        ((selectedCloseChallenges received B A).card:ℚ)/A.card := by
    simpa only [add_zero] using h
  exact h'.trans (div_le_div_of_nonneg_right hc (Nat.cast_nonneg A.card))

/-- The actual field-game probability with any pre-query support is zero
when that support is impossible. This is used for the good-anchor branch,
not as an assumption that acceptance enforces a good anchor. -/
theorem empty_support {q : Nat} (rows : Rows (K := K)) (hq : rows.quarter*4=1)
    (received : Fin 1048576 → K) (strategy : K → Strategy domain q)
    (support : K → K → K → Prop) (never : ∀ k t a, ¬support k t a)
    (A G : Finset K) :
    supportedRowsProbability rows hq (oracle rows.referenceQ received)
      strategy support A G=0 := by
  classical
  simp only [supportedRowsProbability,supportedProbability,if_neg (never _ _ _),avg,
    Finset.sum_const_zero,zero_div]

/-- Replacing only the analysis reference preserves the literal selected
oracle; the indexed received values are identical, not asserted equivalent. -/
theorem replaced_oracle (Q0 Q : Fin 1024 → K) (received : Fin 1048576 → K) :
    replaceOracle (oracle Q0 received) Q=oracle Q received := rfl

/-- Geometry supplies representation. The image/row theorem then bounds
bad anchors in the ORIGINAL field execution, with its original reference.
There is no supplied `represented` premise in the final dichotomy below. -/
theorem dense_bad_bound {q : Nat} (received : Fin 1048576 → K) (B : Nat)
    (Q : Fin 1024 → K)
    (represents : ∀ alpha : K, ∀ final : Fin 256 → K,
      (foldedBad exactFinalLinear (canonicalOneFoldSchedule 0).circleInv2x
        (canonicalOneFoldSchedule 0).circleInv2y received alpha final).card≤B →
      final=coefficientFoldLayer 256 alpha Q)
    (rows : Rows (K := K)) (hq : rows.quarter*4=1)
    (strategy : K → Strategy domain q) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hpos : 0<q) (hcount : q≤domain.card) :
    supportedRowsProbability rows hq (oracle rows.referenceQ received) strategy
      (fun k t a => near received B strategy k t a ∧ badReference (replaceRows rows Q))
      A G ≤ ((q:ℚ)+3)/G.card+24/A.card := by
  classical
  let support := fun k t a => near received B strategy k t a ∧ badReference (replaceRows rows Q)
  change supportedRowsProbability rows hq _ strategy support A G≤_
  by_cases bad : badReference (replaceRows rows Q)
  · rw [← supported_rows_probability rows Q hq (oracle rows.referenceQ received)
      strategy support A G, replaced_oracle]
    apply represented_image_or_rows_bound (replaceRows rows Q) hq (oracle Q received)
      strategy support ?_ A G ha hg hpos hcount bad
    intro k t a hs
    exact represents a ((strategy k).final t a) hs.1
  · rw [empty_support rows hq received strategy support (fun _ _ _ h => bad h.2) A G]
    positivity

/-- TOTAL near-final class decomposition for the actual selected received
word and the constructed compact relation game. In the dense case the
remaining good-anchor executions are NOT bounded here: their component and
payment recovery obligations remain. Far-final executions are also outside
this explicitly supported event. Q is chosen before every strategy input. -/
theorem geometric_joint_dichotomy (received : Fin 1048576 → K) (B : Nat)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (margin : 5*B+255<262144) :
    ((selectedCloseChallenges received B A).card≤3 ∧
      ∀ (q : Nat) (rows : Rows (K := K)) (hq : rows.quarter*4=1)
        (strategy : K → Strategy domain q), q≤domain.card →
        supportedRowsProbability rows hq (oracle rows.referenceQ received)
          strategy (near received B strategy) A G≤3/A.card) ∨
    (3 < (selectedCloseChallenges received B A).card ∧ ∃ Q : Fin 1024 → K,
      (fibreBad (m := 262144) (exactInitialEncoder Q) received).card≤4*B ∧
      (∀ alpha : K, ∀ final : Fin 256 → K,
        (foldedBad exactFinalLinear (canonicalOneFoldSchedule 0).circleInv2x
          (canonicalOneFoldSchedule 0).circleInv2y received alpha final).card≤B →
        final=coefficientFoldLayer 256 alpha Q) ∧
      ∀ (q : Nat) (rows : Rows (K := K)) (hq : rows.quarter*4=1)
        (strategy : K → Strategy domain q), 0<q → q≤domain.card →
        supportedRowsProbability rows hq (oracle rows.referenceQ received) strategy
          (fun k t a => near received B strategy k t a ∧ badReference (replaceRows rows Q))
          A G≤((q:ℚ)+3)/G.card+24/A.card) := by
  by_cases sparse : (selectedCloseChallenges received B A).card≤3
  · exact Or.inl ⟨sparse, fun q rows hq strategy hcount =>
      sparse_near_bound received B rows hq strategy A G ha hg hcount sparse⟩
  · rcases pre_tau_geometric_anchor_dichotomy received B A margin with impossible | ⟨Q, close, rep⟩
    · exact False.elim (sparse impossible)
    · exact Or.inr ⟨by omega, Q, close, rep, fun q rows hq strategy hpos hcount =>
        dense_bad_bound received B Q rep rows hq strategy A G ha hg hpos hcount⟩

#print axioms sparse_near_bound
#print axioms empty_support
#print axioms replaced_oracle
#print axioms dense_bad_bound
#print axioms geometric_joint_dichotomy
end
end AspisV8.PreAnchorJoint
