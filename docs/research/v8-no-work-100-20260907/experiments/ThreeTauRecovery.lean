import SevenAlphaRecovery
import RobustImageGame

/-! Deterministic image separation from a common-support fork grid.
One quotient is constructed, then used across all tau/alpha branches. The
ordinary prefix is fixed before tau; each first response may depend on tau,
and each final on tau and alpha. No supplied quotient, image validity,
provider success, authentication law, or probability bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.ThreeTauAlgebra
open Finset Polynomial
open AspisV8.FirstImageDiscrepancy AspisV8.ReferenceIndependentRelation
open AspisV8.JointImageGame AspisV5FriRelationCandidateBridge
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]

/-- Three zero evaluations of the SAME mixed image polynomial separate its
constant ordinary discrepancy and both image coefficients. No probability
root bound is inferred for this analysis quotient. -/
theorem three_mixed_equations (pre : Before (K := K)) (Q : Fin 1024 → K)
    (taus : Finset K) (three : 3≤taus.card)
    (mixed : ∀ tau∈taus,
      pre.claim-candidateClaim pre.ordinary Q-tau*Q 1023-
        tau^2*(pre.b*Q 1022-pre.c*Q 1021)=0) :
    (replaceBefore pre Q).errorPolynomial=0 ∧
      pre.claim=candidateClaim pre.ordinary Q ∧
      Q 1023=0 ∧ pre.b*Q 1022-pre.c*Q 1021=0 := by
  classical
  have zeros (tau : K) (member : tau∈taus) :
      (replaceBefore pre Q).errorPolynomial.eval tau=0 := by
    change (imagePolynomial (pre.claim-candidateClaim pre.ordinary Q)
      (Q 1023) (pre.b*Q 1022-pre.c*Q 1021)).eval tau=0
    rw [imagePolynomial_eval]
    exact mixed tau member
  have identity : (replaceBefore pre Q).errorPolynomial=0 := by
    by_contra nonzero
    have inclusion : taus⊆taus.filter (fun tau =>
        (replaceBefore pre Q).errorPolynomial.eval tau=0) := by
      intro tau member
      exact Finset.mem_filter.mpr ⟨member,zeros tau member⟩
    have roots := root_count taus (replaceBefore pre Q).errorPolynomial nonzero 2
      (error_degree _)
    have card := Finset.card_le_card inclusion
    omega
  have none : ¬(pre.claim-candidateClaim pre.ordinary Q≠0 ∨
      Q 1023≠0 ∨ pre.b*Q 1022-pre.c*Q 1021≠0) := by
    intro wrong
    exact RobustImageGame.image_nonzero_any _ _ _ wrong identity
  have ordinary : pre.claim-candidateClaim pre.ordinary Q=0 := by
    by_contra wrong
    exact none (Or.inl wrong)
  have e1 : Q 1023=0 := by
    by_contra wrong
    exact none (Or.inr (Or.inl wrong))
  have e2 : pre.b*Q 1022-pre.c*Q 1021=0 := by
    by_contra wrong
    exact none (Or.inr (Or.inr wrong))
  exact ⟨identity,sub_eq_zero.mp ordinary,e1,e2⟩

#print axioms three_mixed_equations
end AspisV8.ThreeTauAlgebra

namespace AspisV8.ThreeTauRecovery
open Finset
open AspisV8.FirstImageDiscrepancy AspisV8.PostQueryFunctional
open AspisV8.ReferenceIndependentRelation AspisV8.OptimizedRelationRefinement
open AspisV8.SevenAlphaRecovery
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity AspisV5ComponentCQM31TowerExact
open AspisV5FriConcreteEncoderCommutation AspisV5FriRelationCandidateBridge
noncomputable section
local instance : NeZero (2 : QM31Exact) := AspisV8.SelectedReceivedOracle.twoNonzero

/-- One selected quotient is reconstructed from the first tau's branches.
Its agreement on the SAME received-word support identifies every later
adaptive final directly, so no independent Q_tau uniqueness premise occurs.
The result binds the actual carried image and ordinary scalar separately. -/
theorem three_tau_common_support
    (received : Fin 1048576 → QM31Exact) (S : Finset (Fin 262144))
    (large : 255<S.card) (taus : Finset QM31Exact) (three : 3≤taus.card)
    (nodes : QM31Exact → Finset QM31Exact)
    (seven : ∀ tau∈taus, 7≤(nodes tau).card)
    (pre : Before (K := QM31Exact)) (hq : pre.quarter*4=1)
    (sent : QM31Exact → Sent QM31Exact)
    (final : QM31Exact → QM31Exact → Fin 256 → QM31Exact)
    (matched : ∀ tau∈taus, ∀ alpha∈nodes tau, ∀ i∈S,
      exactFinalLinear (final tau alpha) i=circleFoldLayer 262144 alpha
        (canonicalOneFoldSchedule 0).circleInv2x
        (canonicalOneFoldSchedule 0).circleInv2y received i)
    (zeroPrior : ∀ tau∈taus, ∀ alpha∈nodes tau,
      (pre.snapshot tau (sent tau) alpha).prior (final tau alpha)=0) :
    ∃ Q : Fin 1024 → QM31Exact,
      (∀ i∈S, ∀ slot : Fin 4,
        exactInitialEncoder Q (childIndex i slot)=received (childIndex i slot)) ∧
      (∀ tau∈taus, ∀ alpha∈nodes tau,
        final tau alpha=coefficientFoldLayer 256 alpha Q) ∧
      (∀ tau∈taus, (replaceBefore pre Q).firstError tau (sent tau)=0) ∧
      (replaceBefore pre Q).errorPolynomial=0 ∧
      pre.claim=candidateClaim pre.ordinary Q ∧
      Q 1023=0 ∧ pre.b*Q 1022-pre.c*Q 1021=0 := by
  have nonempty : taus.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨tau0,member0⟩ := nonempty
  obtain ⟨Q,recovered,_,_,_⟩ := seven_alpha_common_support received S large
    (nodes tau0) (seven tau0 member0) (final tau0) pre hq tau0 (sent tau0)
    (matched tau0 member0) (zeroPrior tau0 member0)
  have represented : ∀ tau∈taus, ∀ alpha∈nodes tau,
      final tau alpha=coefficientFoldLayer 256 alpha Q := by
    intro tau member alpha ha
    exact common_support_identifies received S large Q recovered alpha (final tau alpha)
      (matched tau member alpha ha)
  have consistent (tau : QM31Exact) (member : tau∈taus) :
      (replaceBefore pre Q).firstError tau (sent tau)=0 ∧
        pre.claim-candidateClaim pre.ordinary Q-tau*Q 1023-
          tau^2*(pre.b*Q 1022-pre.c*Q 1021)=0 :=
    SevenAlphaAlgebra.seven_represented_priors pre hq tau (sent tau)
      (nodes tau) (seven tau member) (final tau) Q (represented tau member)
      (zeroPrior tau member)
  obtain ⟨identity,ordinary,e1,e2⟩ := ThreeTauAlgebra.three_mixed_equations pre Q taus three
    (fun tau member => (consistent tau member).2)
  exact ⟨Q,recovered,represented,(fun tau member => (consistent tau member).1),
    identity,ordinary,e1,e2⟩

#print axioms three_tau_common_support
end
end AspisV8.ThreeTauRecovery
