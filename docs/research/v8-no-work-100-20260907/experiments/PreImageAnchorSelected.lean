import PreImageAnchor
import PartialFoldSelected

/-! Selected stored circle/line specialization, reusing the proved V7
natural encoder commutation, canonical inverse tables and final overlap cap.
The full quotient anchor is constructed, not supplied by a provider. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.PreImageAnchorSelected

open AspisV8.PreImageAnchor
open AspisV8.PartialFoldRecovery
open AspisV8.PartialFoldSelected
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5FriConcreteEncoderCommutation

noncomputable section

/-- All eligibility and choice inputs are fixed before the image challenge.
The dense branch captures every close final even if chosen after tau/alpha. -/
theorem pre_tau_geometric_anchor_dichotomy
    (received : Fin 1048576 → QM31Exact) (B : Nat) (challenges : Finset QM31Exact)
    (margin : 5*B+255 < 262144) :
    (selectedCloseChallenges received B challenges).card ≤ 3 ∨
      ∃ anchor : Fin 1024 → QM31Exact,
        (fibreBad (m := 262144) (exactInitialEncoder anchor) received).card ≤ 4*B ∧
        ∀ alpha : QM31Exact, ∀ final : Fin 256 → QM31Exact,
          (foldedBad exactFinalLinear (canonicalOneFoldSchedule 0).circleInv2x
            (canonicalOneFoldSchedule 0).circleInv2y received alpha final).card ≤ B →
          final = coefficientFoldLayer 256 alpha anchor := by
  have inverse := canonical_one_fold_schedule_exact 0
  have split := geometric_anchor_dichotomy exactFinalLinear exactCircleX exactCircleY
    (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y inverse.1 inverse.2 255 B
    exactFinalEncoder_overlap_cap margin received challenges
  rcases split with sparse | ⟨anchor, distance, represents⟩
  · exact Or.inl sparse
  · right
    refine ⟨anchor, ?_, represents⟩
    rw [congrFun exactInitialEncoder_eq_circleLift anchor]
    exact distance

/-- B=2325 puts the constructed full quotient within 9300 complete fibres,
inside the earlier 9301 near-anchor regime, without claiming its image. -/
theorem pre_tau_2325_anchor
    (received : Fin 1048576 → QM31Exact) (challenges : Finset QM31Exact) :
    (selectedCloseChallenges received 2325 challenges).card ≤ 3 ∨
      ∃ anchor : Fin 1024 → QM31Exact,
        (fibreBad (m := 262144) (exactInitialEncoder anchor) received).card ≤ 9300 ∧
        ∀ alpha : QM31Exact, ∀ final : Fin 256 → QM31Exact,
          (foldedBad exactFinalLinear (canonicalOneFoldSchedule 0).circleInv2x
            (canonicalOneFoldSchedule 0).circleInv2y received alpha final).card ≤ 2325 →
          final = coefficientFoldLayer 256 alpha anchor :=
  pre_tau_geometric_anchor_dichotomy received 2325 challenges (by omega)

#print axioms pre_tau_geometric_anchor_dichotomy
#print axioms pre_tau_2325_anchor

end
end AspisV8.PreImageAnchorSelected
