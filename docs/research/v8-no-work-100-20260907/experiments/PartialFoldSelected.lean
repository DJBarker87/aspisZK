import PartialFoldRecovery
import ExactFoldSelected

/-! Exact selected log20/log18 specialization of common-support recovery.
The full quotient code is not restricted to image-valid reconstruction.
Actual-source/FS coupling and the relation/semantic checks remain separate. -/

set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.PartialFoldSelected

open AspisV8.PartialFoldRecovery
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5FriConcreteEncoderCommutation

noncomputable section

def selectedCloseChallenges (received : Fin 1048576 → QM31Exact)
    (B : Nat) (challenges : Finset QM31Exact) : Finset QM31Exact :=
  closeFoldChallenges exactFinalLinear
    (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y received B challenges

/-- All slots of the actual natural1024 encoder are reconstructed on the
common support; no exact-polynomial received-word assumption is used. -/
theorem four_selected_support_folds_recover
    (received : Fin 1048576 → QM31Exact) (nodes : Finset QM31Exact)
    (four : nodes.card=4) (final : QM31Exact → Fin 256 → QM31Exact)
    (support : Set (Fin 262144))
    (matched : ∀ a ∈ nodes, ∀ i ∈ support,
      exactFinalLinear (final a) i = circleFoldLayer 262144 a
        (canonicalOneFoldSchedule 0).circleInv2x
        (canonicalOneFoldSchedule 0).circleInv2y received i) :
    ∃ message : Fin 1024 → QM31Exact, ∀ i ∈ support, ∀ slot : Fin 4,
      exactInitialEncoder message (childIndex i slot) = received (childIndex i slot) := by
  have inverse := canonical_one_fold_schedule_exact 0
  obtain ⟨message, agreement⟩ := four_support_folds_recover exactFinalLinear exactCircleX exactCircleY
    (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y inverse.1 inverse.2
    received nodes four final support matched
  refine ⟨message, ?_⟩
  rw [congrFun exactInitialEncoder_eq_circleLift message]
  exact agreement

theorem four_selected_close_folds_recover
    (received : Fin 1048576 → QM31Exact) (nodes : Finset QM31Exact)
    (four : nodes.card=4) (final : QM31Exact → Fin 256 → QM31Exact) (B : Nat)
    (close : ∀ a ∈ nodes,
      (foldedBad exactFinalLinear (canonicalOneFoldSchedule 0).circleInv2x
        (canonicalOneFoldSchedule 0).circleInv2y received a (final a)).card ≤ B) :
    ∃ message : Fin 1024 → QM31Exact,
      (fibreBad (m := 262144) (exactInitialEncoder message) received).card ≤ 4*B := by
  have inverse := canonical_one_fold_schedule_exact 0
  obtain ⟨message, distance⟩ := four_close_folds_recover exactFinalLinear exactCircleX exactCircleY
    (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y inverse.1 inverse.2
    received nodes four final B close
  refine ⟨message, ?_⟩
  rw [congrFun exactInitialEncoder_eq_circleLift message]
  exact distance

/-- Outside radius 4B in complete original fibres, at most three alpha
values admit any B-close final on the actual final-domain positions. -/
theorem far_selected_close_challenges_le_three
    (received : Fin 1048576 → QM31Exact) (B : Nat) (challenges : Finset QM31Exact)
    (far : ∀ message : Fin 1024 → QM31Exact,
      4*B < (fibreBad (m := 262144) (exactInitialEncoder message) received).card) :
    (selectedCloseChallenges received B challenges).card ≤ 3 := by
  have inverse := canonical_one_fold_schedule_exact 0
  apply far_close_fold_challenges_le_three exactFinalLinear exactCircleX exactCircleY
    (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y inverse.1 inverse.2 received B challenges
  intro message
  rw [← congrFun exactInitialEncoder_eq_circleLift message]
  exact far message

#print axioms four_selected_support_folds_recover
#print axioms four_selected_close_folds_recover
#print axioms far_selected_close_challenges_le_three

end
end AspisV8.PartialFoldSelected
