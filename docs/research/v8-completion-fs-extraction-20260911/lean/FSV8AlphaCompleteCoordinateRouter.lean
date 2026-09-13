import FSV8ExactRootCursor
import AspisFormal.K1.V7Tag73K15RelationAlphaPreAnswerRouters

/-!
# Complete causal coordinate router for the V8 alpha0 sampler

The selected V8 alpha0 is one ordinary bounded Tag-73/QM31 challenge.  One
successful attempt can consume between one and four answer-dependent duplex
pairs.  This leaf attaches the existing V7 eight-coordinate history router
to the *same* forward V8 root cursor introduced in `FSV8ExactRootCursor`.

The coordinate equivalence retains four output blocks, four advance-answer
ghosts, and the complete residual master tape.  It therefore does not make
the false inference that the first squeeze pair alone makes alpha0 uniform.

This is a routing construction, not yet the source-coupling theorem: a later
leaf must prove that every coordinate consumed by a successful V8 alpha0 run
is either routed here as a fresh master-tape answer or belongs to an explicit
cached/collision target event.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1600

namespace AspisV8Completion.FSV8AlphaCompleteCoordinateRouter

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open FSV8ExactRootCursor
open FSBoundedTranscript

noncomputable section

abbrev Block := FSBoundedTranscript.Block

/-- The V8 alpha0 marker has the same literal Tag-73 absorb framing consumed
by the V7 history phase recognizer.  The nonce payload is deliberately left
arbitrary here; only the already-absorbed prefix and label determine the cut.
-/
theorem v8_alpha0_marker_is_round_zero
    (digest : Block) (nonce : List UInt8) :
    relationAlphaMarkerOfInput?
        (List.ofFn digest ++ [0, 20] ++ (0 :: nonce)) = some 0 := by
  have label :
      AspisK1.V7Tag73K15SemanticSequentialRouter.semanticAbsorbLabelOfInput?
          (List.ofFn digest ++ (0 : UInt8) :: 20 :: 0 :: nonce) = some 20 := by
    simpa only [AspisK1.V7Tag73TranscriptSchedule.bytes,
      AspisK1.V7Tag73TranscriptSchedule.domAbsorb,
      List.append_assoc, List.cons_append, List.nil_append] using
      AspisK1.V7Tag73K15SemanticSequentialRouter.literal_semantic_absorb_label
        digest 20 (0 :: nonce)
  have labelAssociated :
      AspisK1.V7Tag73K15SemanticSequentialRouter.semanticAbsorbLabelOfInput?
          (List.ofFn digest ++ [0, 20] ++ (0 :: nonce)) = some 20 := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using label
  unfold relationAlphaMarkerOfInput?
  simp only [AspisK1.V7Tag73TranscriptSchedule.foldWorkNonceLabel,
    labelAssociated,
    if_pos]

/-- Full eight-coordinate causal router over the exact same-body V8 exposure
cursor.  The label is history-sensitive and follows all bounded sentinel
retries of round zero. -/
def alpha0Router
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (hidden : HiddenTape) :=
  (relationAlphaSlotMachine 0 transitionFuel).fullRouter
    (relationAlphaRouterResidual parameters)
    (exposureCursor configuration hidden)

/-- Exact master-tape decomposition for the complete V8 alpha0 attempt:
eight routed duplex coordinates plus every other exposure coordinate. -/
def alpha0Coordinates
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (hidden : HiddenTape) :
    FreshAnswerTape FSBoundedTranscript.Block
        (exactCompilerTargetCaps parameters).length ≃
      (RelationAlphaDuplexSlot → FSBoundedTranscript.Block) ×
        FreshAnswerTape FSBoundedTranscript.Block
          (relationAlphaRouterResidual parameters) :=
  (castFreshAnswerTape (relation_alpha_slots_add_residual parameters).symm).trans
    ((relationAlphaSlotMachine 0 transitionFuel).fullCoordinateEquiv
      (relationAlphaRouterResidual parameters)
      (exposureCursor configuration hidden))

/-- Probability-adapter order: arbitrary residual context first, followed by
the complete four-output/four-advance ordinary sampler tape expected by the
existing V7 factorization theorem. -/
def alpha0SamplerCoordinates
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (hidden : HiddenTape) :
    FreshAnswerTape FSBoundedTranscript.Block
        (exactCompilerTargetCaps parameters).length ≃
      FreshAnswerTape FSBoundedTranscript.Block
          (relationAlphaRouterResidual parameters) ×
        RelationAlphaTotalTape :=
  (alpha0Coordinates parameters configuration transitionFuel hidden).trans
    ((Equiv.prodCongr relationAlphaDuplexTapeEquiv (Equiv.refl _)).trans
      (Equiv.prodComm _ _))

/-- The routed coordinates are attached to the literal erasure of the exact
result-carrying V8 root, not to an independently supplied transcript. -/
theorem exact_root_trace_uses_alpha0_router_source
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (runExactRoot parameters configuration transitionFuel sample).trace =
      runUnifiedExposureTrace transitionFuel
        (exactCompilerTargetCaps parameters).length
        (exposureCursor configuration sample.1) sample.2 := by
  exact run_exact_root_trace_is_erased_exposure_trace parameters configuration
    transitionFuel sample

#print axioms v8_alpha0_marker_is_round_zero
#print axioms alpha0Router
#print axioms alpha0Coordinates
#print axioms alpha0SamplerCoordinates
#print axioms exact_root_trace_uses_alpha0_router_source

end
end AspisV8Completion.FSV8AlphaCompleteCoordinateRouter
