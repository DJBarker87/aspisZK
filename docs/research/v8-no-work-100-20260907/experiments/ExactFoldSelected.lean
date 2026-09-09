import ExactFoldRecovery
import AspisFormal.K1.V7Tag73CanonicalOneFoldSchedule

/-!
The selected mathematical log20/log18 circle/line encoders, not an assumed
code model. The received word is fixed before alpha; final messages may be
chosen after alpha. FullQuotient is the full natural1024 code, not the
codimension-two image-valid quotient subspace. Rust/source and FS coupling
remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.ExactFoldSelected

open AspisV8.ExactFoldRecovery
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriConcreteEncoderCommutation

noncomputable section

def FullQuotient (received : Fin 1048576 → QM31Exact) : Prop :=
  ∃ message : Fin 1024 → QM31Exact, exactInitialEncoder message = received

def selectedChallenges (received : Fin 1048576 → QM31Exact)
    (challenges : Finset QM31Exact) : Finset QM31Exact :=
  exactFoldChallenges exactFinalLinear
    (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y received challenges

/-- The full code event is identified by the existing exact stored-domain
V7 natural encoder/lift theorem, with no membership premise supplied. -/
theorem fullQuotient_iff_lift (received : Fin 1048576 → QM31Exact) :
    FullQuotient received ↔
      received ∈ LinearMap.range (circleLiftEncoder exactFinalLinear exactCircleX exactCircleY) := by
  constructor
  · rintro ⟨message, same⟩
    exact ⟨message, (congrFun exactInitialEncoder_eq_circleLift message).symm.trans same⟩
  · rintro ⟨message, same⟩
    exact ⟨message, (congrFun exactInitialEncoder_eq_circleLift message).trans same⟩

/-- Four distinct globally exact folds construct actual natural1024
coefficients for the received quotient, including every stored slot. -/
theorem four_selected_folds_recover (received : Fin 1048576 → QM31Exact)
    (challenges : Finset QM31Exact)
    (many : 4 ≤ (selectedChallenges received challenges).card) :
    FullQuotient received := by
  have inverse := canonical_one_fold_schedule_exact 0
  apply (fullQuotient_iff_lift received).mpr
  exact four_exact_folds_recover_received exactFinalLinear exactCircleX exactCircleY
    (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y inverse.1 inverse.2 received challenges many

/-- A fixed received word outside the actual full quotient code has at most
three challenges with any globally matching final256 polynomial. -/
theorem nonpolynomial_selected_challenges_le_three
    (received : Fin 1048576 → QM31Exact) (challenges : Finset QM31Exact)
    (outside : ¬ FullQuotient received) :
    (selectedChallenges received challenges).card ≤ 3 := by
  by_contra larger
  exact outside (four_selected_folds_recover received challenges (by omega))

/-- Explicit adaptive final-selection corollary. No final is frozen before
its alpha; only the received word is fixed across the challenge experiment. -/
theorem adaptive_selected_final_matches_le_three
    (received : Fin 1048576 → QM31Exact) (challenges : Finset QM31Exact)
    (outside : ¬ FullQuotient received) (final : QM31Exact → Fin 256 → QM31Exact) :
    (challenges.filter fun alpha => exactFinalLinear (final alpha) =
      circleFoldLayer 262144 alpha (canonicalOneFoldSchedule 0).circleInv2x
        (canonicalOneFoldSchedule 0).circleInv2y received).card ≤ 3 := by
  classical
  have inverse := canonical_one_fold_schedule_exact 0
  exact adaptive_global_final_matches_le_three exactFinalLinear exactCircleX exactCircleY
    (canonicalOneFoldSchedule 0).circleInv2x
    (canonicalOneFoldSchedule 0).circleInv2y inverse.1 inverse.2 received challenges
    (fun inside => outside ((fullQuotient_iff_lift received).mpr inside)) final

#print axioms fullQuotient_iff_lift
#print axioms four_selected_folds_recover
#print axioms nonpolynomial_selected_challenges_le_three
#print axioms adaptive_selected_final_matches_le_three

end
end AspisV8.ExactFoldSelected
