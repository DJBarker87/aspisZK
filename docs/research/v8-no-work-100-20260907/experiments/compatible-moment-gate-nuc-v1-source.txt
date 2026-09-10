import RelationCompatibleMoment

/-! The actual relation-compatible moment retains the full matching mass
when its prior is zero. A literal six-zero compact response, zero incoming
claim and zero final realize this case causally, for arbitrary alpha/tau
and public weights. No received polynomiality or probability is asserted.
Source-only draft: not yet compiled. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000

namespace AspisV8.CompatibleMomentGate
open AspisV8.RelationCompatibleMoment AspisV8.PostQueryFunctional
open AspisV8.OptimizedRelationRefinement AspisV5FriRelationCandidateBridge
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

theorem compatibleMoment_eq_matching_of_prior_zero (p : Prefix (K := K))
    (final : Fin 256 → K) (received : K → K) (D : Finset K) (q : Nat)
    (zero : p.prior final = 0) :
    compatibleMoment p final received D q = matchingRatio D q final received := by
  simp only [compatibleMoment, if_pos zero]

/-- Sent before alpha: all six actually transmitted fields are zero. -/
def zeroSent : Sent K := ⟨0, 0, 0, 0, 0, 0⟩

theorem zero_next_claim (quarter alpha : K) :
    nextClaim quarter 0 (zeroSent (K := K)) alpha = 0 := by
  rw [nextClaim_source_horner]
  simp only [sourceHorner, zeroSent, zero_mul, mul_zero, zero_add, sub_zero]

/-- The reference vector and transported fold weight need not be unfolded.
The zero final makes the exact dot zero for EVERY such public weight. -/
theorem zero_response_prior (p : Prefix (K := K))
    (claim : p.claim = 0) (sent : p.response0 = zeroSent) :
    p.prior (0 : Fin 256 → K) = 0 := by
  unfold Prefix.prior Prefix.carried
  rw [claim, sent, zero_next_claim]
  simp only [candidateClaim, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]

theorem zero_response_moment (p : Prefix (K := K))
    (claim : p.claim = 0) (sent : p.response0 = zeroSent)
    (received : K → K) (D : Finset K) (q : Nat) :
    compatibleMoment p (0 : Fin 256 → K) received D q =
      matchingRatio D q (0 : Fin 256 → K) received :=
  compatibleMoment_eq_matching_of_prior_zero p _ received D q
    (zero_response_prior p claim sent)

#print axioms compatibleMoment_eq_matching_of_prior_zero
#print axioms zero_next_claim
#print axioms zero_response_prior
#print axioms zero_response_moment
end
end AspisV8.CompatibleMomentGate
