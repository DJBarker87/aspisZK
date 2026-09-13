import FSV8AlphaTotalSuccessfulCoordinates

/-!
# Exact routed ordinary-alpha event

This leaf instantiates the existing complete causal ordinary-sampler event on
the exact V8 alpha-zero coordinate router.  It defines the event that the
routed total tape succeeds and its successful sample lies in a
residual/skeleton-dependent target, then obtains the existing exact
`cap / P^4` bound.

This is deliberately not an accepted-verifier theorem.  The remaining source
obligation is to prove that the relevant accepted bad-alpha executions either
belong to this event or to the already charged exact-root target event.  No
such coverage premise is introduced here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 1500

namespace AspisV8Completion.FSV8AlphaOrdinaryRoutedEvent

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact
open FSV8AlphaCompleteCoordinateRouter
open FSV8AlphaTotalSuccessfulCoordinates
open FSV8ExactRootCursor

noncomputable section

abbrev Alpha0Residual (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256 (relationAlphaRouterResidual parameters)

/-- The literal probability-consumer event induced by the V8 alpha-zero
coordinate equivalence.  The target may depend on the hidden tape, every
residual answer, and the complete rejection/advance nuisance skeleton, but
not on the isolated returned ordinary value. -/
def alpha0OrdinaryRoutedEvent
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (target : HiddenTape → Alpha0Residual parameters →
      Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample |
    alpha0SamplerCoordinates parameters configuration transitionFuel sample.1
        sample.2 ∈
      dependentSuccessfulSubtypeEvent relationAlphaTotalSucceeds
        (fun residual ↦ successfulRelationAlphaTotalEquiv ⁻¹'
          duplexOrdinaryDependentEvent (target sample.1 residual))}

theorem mem_alpha0OrdinaryRoutedEvent_iff
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (target : HiddenTape → Alpha0Residual parameters →
      Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (sample : ExactCompilerSample HiddenTape parameters) :
    sample ∈ alpha0OrdinaryRoutedEvent parameters configuration
        transitionFuel target ↔
      alpha0SamplerCoordinates parameters configuration transitionFuel sample.1
          sample.2 ∈
        dependentSuccessfulSubtypeEvent relationAlphaTotalSucceeds
          (fun residual ↦ successfulRelationAlphaTotalEquiv ⁻¹'
            duplexOrdinaryDependentEvent (target sample.1 residual)) := by
  rfl

/-- Source-facing elimination form of routed-event membership.  A caller must
construct decoder success for the literal routed total coordinate and target
membership for that same successful sample.  This theorem does not manufacture
either fact from acceptance. -/
theorem mem_alpha0OrdinaryRoutedEvent_iff_exists_success
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (target : HiddenTape → Alpha0Residual parameters →
      Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (sample : ExactCompilerSample HiddenTape parameters) :
    sample ∈ alpha0OrdinaryRoutedEvent parameters configuration
        transitionFuel target ↔
      ∃ success : relationAlphaTotalSucceeds
          (alpha0SamplerCoordinates parameters configuration transitionFuel
            sample.1 sample.2).2,
        successfulRelationAlphaTotalEquiv
            ⟨(alpha0SamplerCoordinates parameters configuration transitionFuel
              sample.1 sample.2).2, success⟩ ∈
          duplexOrdinaryDependentEvent
            (target sample.1
              (alpha0SamplerCoordinates parameters configuration transitionFuel
                sample.1 sample.2).1) := by
  rfl

/-- Exact no-work probability bound for the routed event itself.  The source
inclusion from accepted bad-alpha executions is intentionally a later theorem,
not a hypothesis hidden in this statement. -/
theorem alpha0_ordinary_routed_event_probability_le
    {HiddenTape TapeIdentity Observation : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (target : HiddenTape → Alpha0Residual parameters →
      Tag73CompleteOrdinarySamplerSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ hidden residual skeleton,
      (target hidden residual skeleton).card ≤ cap) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (alpha0OrdinaryRoutedEvent parameters configuration transitionFuel
          target) ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply exact_compiler_dependent_ordinary_event_probability_le hiddenLaw
    (exactCompilerTargetCaps parameters).length relationAlphaTotalSucceeds
    (alpha0SamplerCoordinates parameters configuration transitionFuel)
    successfulRelationAlphaTotalEquiv target cap targetCap
  intro hidden answers member
  exact member

#print axioms alpha0OrdinaryRoutedEvent
#print axioms mem_alpha0OrdinaryRoutedEvent_iff
#print axioms mem_alpha0OrdinaryRoutedEvent_iff_exists_success
#print axioms alpha0_ordinary_routed_event_probability_le

end
end AspisV8Completion.FSV8AlphaOrdinaryRoutedEvent
