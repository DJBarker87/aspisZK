import AspisFormal.K1.V7Tag73K13RestrictedJointBatchActualLawClosure

/-!
# Field facts transported across a K1.3 view equality

This lemma is deliberately independent of the scheduler-dependent witness
type. It lets the final alignment constructor transport five already-proved
facts without elaborating their large indices simultaneously.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73K13CandidateDirectedViewFacts

open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisV5ComponentCQM31TowerExact
open AspisV6QueryBatchSoundness

/-- Membership transports contravariantly across equality of finite sets. -/
theorem memLeftOfFinsetEq
    {K : Type*} [DecidableEq K]
    {left right : Finset K} {value : K}
    (targetExact : left = right) (member : value ∈ right) :
    value ∈ left := by
  rw [targetExact]
  exact member

/-- Transport the active flag, three algebraic fields, and collision membership
across equality of two pre-challenge views. -/
theorem alignedFactsOfViewEq
    (currentView witnessView : JointQueryBatchPreChallengeView)
    (viewExact : currentView = witnessView)
    {preQueryDiscrepancy : QM31Exact}
    {expected authenticated : QueryVector QM31Exact}
    {rho : QM31Exact}
    (active : witnessView.active = true)
    (preExact : witnessView.preQueryDiscrepancy = preQueryDiscrepancy)
    (expectedExact : witnessView.expected = expected)
    (authenticatedExact : witnessView.authenticated = authenticated)
    (member : rho ∈ witnessView.collisionTarget) :
    currentView.active = true ∧
      currentView.preQueryDiscrepancy = preQueryDiscrepancy ∧
      currentView.expected = expected ∧
      currentView.authenticated = authenticated ∧
      rho ∈ currentView.collisionTarget := by
  subst currentView
  exact ⟨active, preExact, expectedExact, authenticatedExact, member⟩

#print axioms alignedFactsOfViewEq
#print axioms memLeftOfFinsetEq

end AspisK1.V7Tag73K13CandidateDirectedViewFacts
