import FSV8AlphaCompleteCoordinateRouter
import AspisFormal.K1.V7Tag73CausalMachineLabeledTraceRouting

/-!
# Literal realization of one V8 alpha router coordinate

This leaf specializes the generic causal machine routing theorem to the exact
V8 alpha-zero router.  Given a chronological labelled trace from the exact
root cursor and the literal master-tape prefix consumed by that trace, every
named output/advance slot in the trace is the corresponding component of
`alpha0Coordinates`.

The remaining source theorem must construct the labelled trace and tape-prefix
facts from the same accepted `SuccessfulAlignedChallenge`.  They are not
inferred here from local `.fresh` origins: local freshness after restoration
does not by itself imply use of a globally unexposed master-tape coordinate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AlphaRouterRealization

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8AlphaCompleteCoordinateRouter
open FSV8ExactRootCursor

noncomputable section

abbrev Block := FSBoundedTranscript.Block

/-- Exact deterministic source package still required from the accepted root
run.  Its fields are operational trace facts, not probability or target-event
assumptions. -/
structure Alpha0RootLabeledTrace
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (hidden : HiddenTape)
    (tape : FreshAnswerTape Block
      (exactCompilerTargetCaps parameters).length) : Type 2 where
  steps : List (Option RelationAlphaDuplexSlot × Block)
  finalCursor : UnifiedExposureCursor
    (globalFull256OracleCallCap parameters)
  remaining : List Block
  trace : MachineLabeledTrace (relationAlphaSlotMachine 0 transitionFuel)
    (exposureCursor configuration hidden) steps finalCursor
  namedNodup : (namedTraceSlots steps).Nodup
  residualEnough : residualTraceSteps steps ≤
    relationAlphaRouterResidual parameters
  tapePrefix : freshAnswerTapeToList
      (castFreshAnswerTape
        (relation_alpha_slots_add_residual parameters).symm tape) =
    steps.map Prod.snd ++ remaining

/-- Every named literal source answer in a constructed exact-root trace is
the corresponding component of the exact V8 alpha coordinate equivalence. -/
theorem alpha0_coordinate_eq_of_labeled_trace
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (hidden : HiddenTape)
    (tape : FreshAnswerTape Block
      (exactCompilerTargetCaps parameters).length)
    (source : Alpha0RootLabeledTrace parameters configuration transitionFuel
      hidden tape)
    (prior later : List (Option RelationAlphaDuplexSlot × Block))
    (slot : RelationAlphaDuplexSlot) (answer : Block)
    (decomposition : source.steps =
      prior ++ (some slot, answer) :: later) :
    (alpha0Coordinates parameters configuration transitionFuel hidden tape).1
        slot = answer := by
  let alignedTape := castFreshAnswerTape
    (relation_alpha_slots_add_residual parameters).symm tape
  have routed : causalRoutedAnswer? slot
      (alpha0Router parameters configuration transitionFuel hidden)
      alignedTape = some answer := by
    apply machine_labeled_trace_routes_named_answer source.trace
      source.namedNodup
      (fun named _member ↦ Finset.mem_univ named)
      source.residualEnough alignedTape source.remaining source.tapePrefix
      prior later slot answer decomposition
  change (((relationAlphaSlotMachine 0 transitionFuel).fullCoordinateEquiv
      (relationAlphaRouterResidual parameters)
      (exposureCursor configuration hidden)) alignedTape).1 slot = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some
    (alpha0Router parameters configuration transitionFuel hidden)
    alignedTape slot (Finset.mem_univ slot) answer routed

@[simp] theorem alpha0SamplerCoordinates_output
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (hidden : HiddenTape)
    (tape : FreshAnswerTape Block
      (exactCompilerTargetCaps parameters).length)
    (block : Fin 4) :
    (alpha0SamplerCoordinates parameters configuration transitionFuel hidden
      tape).2.1 block =
    (alpha0Coordinates parameters configuration transitionFuel hidden tape).1
      (block, 0) := by
  rfl

@[simp] theorem alpha0SamplerCoordinates_advance
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (hidden : HiddenTape)
    (tape : FreshAnswerTape Block
      (exactCompilerTargetCaps parameters).length)
    (block : Fin 4) :
    (alpha0SamplerCoordinates parameters configuration transitionFuel hidden
      tape).2.2 block =
    (alpha0Coordinates parameters configuration transitionFuel hidden tape).1
      (block, 1) := by
  rfl

/-- Output-half form used by an accepted aligned alpha run. -/
theorem alpha0_sampler_output_eq_of_labeled_trace
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (hidden : HiddenTape)
    (tape : FreshAnswerTape Block
      (exactCompilerTargetCaps parameters).length)
    (source : Alpha0RootLabeledTrace parameters configuration transitionFuel
      hidden tape)
    (prior later : List (Option RelationAlphaDuplexSlot × Block))
    (block : Fin 4) (answer : Block)
    (decomposition : source.steps =
      prior ++ (some (block, 0), answer) :: later) :
    (alpha0SamplerCoordinates parameters configuration transitionFuel hidden
      tape).2.1 block = answer := by
  rw [alpha0SamplerCoordinates_output]
  exact alpha0_coordinate_eq_of_labeled_trace parameters configuration
    transitionFuel hidden tape source prior later (block, 0) answer
      decomposition

/-- Advance-half form used by an accepted aligned alpha run. -/
theorem alpha0_sampler_advance_eq_of_labeled_trace
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (hidden : HiddenTape)
    (tape : FreshAnswerTape Block
      (exactCompilerTargetCaps parameters).length)
    (source : Alpha0RootLabeledTrace parameters configuration transitionFuel
      hidden tape)
    (prior later : List (Option RelationAlphaDuplexSlot × Block))
    (block : Fin 4) (answer : Block)
    (decomposition : source.steps =
      prior ++ (some (block, 1), answer) :: later) :
    (alpha0SamplerCoordinates parameters configuration transitionFuel hidden
      tape).2.2 block = answer := by
  rw [alpha0SamplerCoordinates_advance]
  exact alpha0_coordinate_eq_of_labeled_trace parameters configuration
    transitionFuel hidden tape source prior later (block, 1) answer
      decomposition

#print axioms Alpha0RootLabeledTrace
#print axioms alpha0_coordinate_eq_of_labeled_trace
#print axioms alpha0SamplerCoordinates_output
#print axioms alpha0SamplerCoordinates_advance
#print axioms alpha0_sampler_output_eq_of_labeled_trace
#print axioms alpha0_sampler_advance_eq_of_labeled_trace

end
end AspisV8Completion.FSV8AlphaRouterRealization
