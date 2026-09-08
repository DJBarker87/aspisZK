import AspisFormal.K1.V7Tag73CausalRawOneFoldProbability

/-! # Lightweight product membership for a successful raw one-fold sample -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73SuccessfulRawOneFoldProductMembership

open AspisK1.V7Tag73CausalRawOneFoldProductProbability
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A named decoded value in its skeleton slice packages into the factorized
product event.  The slice is abstract here so no verifier context is unfolded. -/
theorem mem_factorized_dependentProductEvent_of_value
    (bad : Tag73OrdinarySamplerSkeleton → Set QM31Exact)
    (raw : SuccessfulTag73RawStream)
    (member : successfulOrdinaryExactValue raw ∈
      bad (successfulOrdinaryExactFactorization raw).1) :
    raw ∈ successfulOrdinaryExactFactorization ⁻¹'
      dependentProductEvent bad := by
  change (successfulOrdinaryExactFactorization raw).2 ∈
    bad (successfulOrdinaryExactFactorization raw).1
  rw [successfulOrdinaryExactFactorization_value]
  exact member

/-- Transport exact slice membership across explicit raw-stream and target-
family equalities without unfolding either concrete endpoint. -/
theorem transport_successfulOrdinaryExactTargetMember
    (leftRaw rightRaw : SuccessfulTag73RawStream)
    (leftTarget rightTarget : Tag73OrdinarySamplerSkeleton → Set QM31Exact)
    (rawExact : leftRaw = rightRaw)
    (targetExact : leftTarget = rightTarget)
    (member : successfulOrdinaryExactValue leftRaw ∈
      leftTarget (successfulOrdinaryExactFactorization leftRaw).1) :
    successfulOrdinaryExactValue rightRaw ∈
      rightTarget (successfulOrdinaryExactFactorization rightRaw).1 := by
  subst rightRaw
  subst rightTarget
  exact member

#print axioms mem_factorized_dependentProductEvent_of_value
#print axioms transport_successfulOrdinaryExactTargetMember

end


end AspisK1.V7Tag73SuccessfulRawOneFoldProductMembership
