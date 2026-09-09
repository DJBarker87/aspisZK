import ThreeTauRecovery

/-! Deterministic separation of the repaired inactive/three-point rows.
One quotient is reconstructed from a common-support fork grid, then reused
for every kappa/tau/alpha branch. No quotient, inactiveExact, image validity
or row correctness is supplied. Fork production, authentication, probability
and valid-payment extraction remain separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.FourKappaAlgebra
open Finset Polynomial
open AspisV8.ShiftedRowPrefix AspisV8.ReferenceIndependentRelation
open AspisV8.JointImageGame AspisV5FriRelationCandidateBridge
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]

/-- The literal corrected affine scalar and transported functional determine
the shifted row-error cubic. Four roots separate all four original rows,
including inactive; inactive exactness is a conclusion, not a premise. -/
theorem four_corrected_claims (rows : Rows (K := K)) (Q : Fin 1024 → K)
    (kappas : Finset K) (four : 4≤kappas.card)
    (correct : ∀ kappa∈kappas,
      (rows.before kappa).claim=candidateClaim (rows.before kappa).ordinary Q) :
    (replaceRows rows Q).errorPolynomial=0 ∧
      (replaceRows rows Q).errors=0 ∧
      ∀ j : Fin 4, rows.claimed j=
        rows.functional j (rows.reconstruction Q+rows.interpolant) := by
  classical
  have zeros (kappa : K) (member : kappa∈kappas) :
      (replaceRows rows Q).errorPolynomial.eval kappa=0 := by
    rw [← ShiftedRowPrefix.before_prior]
    change (rows.before kappa).claim-
      candidateClaim (rows.before kappa).ordinary Q=0
    exact sub_eq_zero.mpr (correct kappa member)
  have identity : (replaceRows rows Q).errorPolynomial=0 := by
    by_contra nonzero
    have inclusion : kappas⊆kappas.filter (fun kappa =>
        (replaceRows rows Q).errorPolynomial.eval kappa=0) := by
      intro kappa member
      exact Finset.mem_filter.mpr ⟨member,zeros kappa member⟩
    have roots := root_count kappas (replaceRows rows Q).errorPolynomial nonzero 3
      (ShiftedRowPrefix.error_degree _)
    have card := Finset.card_le_card inclusion
    omega
  have errors : (replaceRows rows Q).errors=0 := by
    by_contra wrong
    exact ShiftedRowPrefix.error_nonzero _ wrong identity
  refine ⟨identity,errors,?_⟩
  intro j
  have value := congrFun errors j
  change rows.claimed j-rows.functional j (rows.reconstruction Q+rows.interpolant)=0 at value
  exact sub_eq_zero.mp value

#print axioms four_corrected_claims
end AspisV8.FourKappaAlgebra

namespace AspisV8.FourKappaRecovery
open Finset
open AspisV8.FirstImageDiscrepancy AspisV8.PostQueryFunctional
open AspisV8.ShiftedRowPrefix AspisV8.ReferenceIndependentRelation
open AspisV8.OptimizedRelationRefinement AspisV8.SevenAlphaRecovery
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity AspisV5ComponentCQM31TowerExact
open AspisV5FriConcreteEncoderCommutation AspisV5FriRelationCandidateBridge
noncomputable section
local instance : NeZero (2 : QM31Exact) := AspisV8.SelectedReceivedOracle.twoNonzero

/-- All prefixes share fixed R, S and the original affine Rows inputs.
The image challenge sets may depend on kappa, alpha sets on kappa/tau,
response0 on kappa/tau, and finals on all revealed challenges. No final is
frozen before its actual alpha. Q is constructed from the first subtree. -/
theorem four_kappa_common_support
    (received : Fin 1048576 → QM31Exact) (S : Finset (Fin 262144))
    (large : 255<S.card) (kappas : Finset QM31Exact) (four : 4≤kappas.card)
    (taus : QM31Exact → Finset QM31Exact)
    (three : ∀ kappa∈kappas, 3≤(taus kappa).card)
    (nodes : QM31Exact → QM31Exact → Finset QM31Exact)
    (seven : ∀ kappa∈kappas, ∀ tau∈taus kappa, 7≤(nodes kappa tau).card)
    (rows : Rows (K := QM31Exact)) (hq : rows.quarter*4=1)
    (sent : QM31Exact → QM31Exact → Sent QM31Exact)
    (final : QM31Exact → QM31Exact → QM31Exact → Fin 256 → QM31Exact)
    (matched : ∀ kappa∈kappas, ∀ tau∈taus kappa, ∀ alpha∈nodes kappa tau, ∀ i∈S,
      exactFinalLinear (final kappa tau alpha) i=circleFoldLayer 262144 alpha
        (canonicalOneFoldSchedule 0).circleInv2x
        (canonicalOneFoldSchedule 0).circleInv2y received i)
    (zeroPrior : ∀ kappa∈kappas, ∀ tau∈taus kappa, ∀ alpha∈nodes kappa tau,
      ((rows.before kappa).snapshot tau (sent kappa tau) alpha).prior
        (final kappa tau alpha)=0) :
    ∃ Q : Fin 1024 → QM31Exact,
      (∀ i∈S, ∀ slot : Fin 4,
        exactInitialEncoder Q (childIndex i slot)=received (childIndex i slot)) ∧
      (∀ kappa∈kappas, ∀ tau∈taus kappa, ∀ alpha∈nodes kappa tau,
        final kappa tau alpha=coefficientFoldLayer 256 alpha Q) ∧
      (replaceRows rows Q).errorPolynomial=0 ∧
      (replaceRows rows Q).errors=0 ∧
      (∀ j : Fin 4, rows.claimed j=
        rows.functional j (rows.reconstruction Q+rows.interpolant)) ∧
      Q 1023=0 ∧ rows.b*Q 1022-rows.c*Q 1021=0 := by
  have nonempty : kappas.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨kappa0,member0⟩ := nonempty
  obtain ⟨Q,recovered,_,_,_,_,e1,e2⟩ :=
    ThreeTauRecovery.three_tau_common_support received S large
      (taus kappa0) (three kappa0 member0) (nodes kappa0) (seven kappa0 member0)
      (rows.before kappa0) hq (sent kappa0) (final kappa0)
      (matched kappa0 member0) (zeroPrior kappa0 member0)
  have represented : ∀ kappa∈kappas, ∀ tau∈taus kappa, ∀ alpha∈nodes kappa tau,
      final kappa tau alpha=coefficientFoldLayer 256 alpha Q := by
    intro kappa member tau ht alpha ha
    exact common_support_identifies received S large Q recovered alpha (final kappa tau alpha)
      (matched kappa member tau ht alpha ha)
  have correct (kappa : QM31Exact) (member : kappa∈kappas) :
      (rows.before kappa).claim=candidateClaim (rows.before kappa).ordinary Q := by
    have mixed (tau : QM31Exact) (ht : tau∈taus kappa) :
        (rows.before kappa).claim-candidateClaim (rows.before kappa).ordinary Q-tau*Q 1023-
          tau^2*((rows.before kappa).b*Q 1022-(rows.before kappa).c*Q 1021)=0 :=
      (SevenAlphaAlgebra.seven_represented_priors (rows.before kappa) hq tau
        (sent kappa tau) (nodes kappa tau) (seven kappa member tau ht)
        (final kappa tau) Q (represented kappa member tau ht)
        (zeroPrior kappa member tau ht)).2
    exact (ThreeTauAlgebra.three_mixed_equations (rows.before kappa) Q
      (taus kappa) (three kappa member) mixed).2.1
  obtain ⟨identity,errors,claims⟩ := FourKappaAlgebra.four_corrected_claims
    rows Q kappas four correct
  exact ⟨Q,recovered,represented,identity,errors,claims,e1,e2⟩

#print axioms four_kappa_common_support
end
end AspisV8.FourKappaRecovery
