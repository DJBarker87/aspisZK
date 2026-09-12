import AspisFormal.K1.V7Tag73ExactRestoredGammaPreActivationPrefix
import AspisFormal.K1.V7Tag73GammaRestoredK14InitialLaneFunctional

/-!
# Pointwise pre-activation source for restored-gamma K1.4

This module replaces the pairwise `sameInitialLanes` source boundary with a
pointwise production projection.  A single literal execution must show that
its 29 initial lanes are a deterministic function of the exact record prefix
before the earliest gamma exposure.  The causal-prefix theorem then proves
that any two executions in one non-gamma residual fibre supply the same
prefix, so pairwise lane equality is derived rather than assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73GammaRestoredK14PreActivationLaneSource

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactRestoredGammaPreActivationPrefix
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14InitialLaneAlignment
open AspisK1.V7Tag73GammaRestoredK14InitialLaneFunctional
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredChallengeCausalMarker
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Source-facing pointwise boundary.  `lanesAtPrefix` is the only production
projection still required for lane functionality: it talks about one actual
execution and one literal pre-activation prefix, never two counterfactual
executions or the conclusion of the K1.4 probability theorem. -/
structure ExactTag73GammaRestoredK14PreActivationLaneSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (canonicalDriverFuel transitionFuel : Nat)
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (rounds : Nat)
    (extractor : ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
      Payload Witness)
    (withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap)
    (adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor
          withinForkCap))
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  roundsPositive : 0 < rounds
  defaultLanes : Width29InitialLanes
  defaultResponse : InitialMessage QM31Exact
  lanesFromPrefix : HiddenTape → List UnifiedExposureRecord →
    Width29InitialLanes
  namedCompleteAt : ∀ (hidden : HiddenTape)
      (answers : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (_cleanMember : (hidden, answers) ∈ clean)
      (_input : ExactK12OperationalInput transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
        projection fixedInstance (hidden, answers)),
    (namedTraceSlots
      (exactRestoredGammaFullLabels transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
        (hidden, answers))).length = 24
  decoderAt : ∀ (hidden : HiddenTape)
      (answers : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (_cleanMember : (hidden, answers) ∈ clean)
      (input : ExactK12OperationalInput transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
        projection fixedInstance (hidden, answers))
      (k13 : ExactGammaRestoredOperationalK13Certificate decoder input)
      (_failure : Width29DecompositionFailure decoder
        k13.certificate.classified.k12.words
        (restoredOperationalK13View k13.certificate.data).gamma
        (restoredOperationalK13View k13.certificate.data).disclosedFinal
        (restoredOperationalK13View k13.certificate.data).schedule),
    ∃ decoded : OrdinaryPrefixDecode,
      runGammaPrefix
          (exactCompilerRestoredGammaCoordinates transitionFuel
            (exactRootSweepWitnessConfiguration base rounds extractor
              withinForkCap) hidden answers).2 = some decoded ∧
      decoded.value = k13.certificate.data.gammaBytes
  lanesAtPrefix : ∀ (hidden : HiddenTape)
      (answers : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (_cleanMember : (hidden, answers) ∈ clean)
      (input : ExactK12OperationalInput transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
        projection fixedInstance (hidden, answers))
      (k13 : ExactGammaRestoredOperationalK13Certificate decoder input)
      (_failure : Width29DecompositionFailure decoder
        k13.certificate.classified.k12.words
        (restoredOperationalK13View k13.certificate.data).gamma
        (restoredOperationalK13View k13.certificate.data).disclosedFinal
        (restoredOperationalK13View k13.certificate.data).schedule)
      (prior later : List UnifiedExposureRecord)
      (record : UnifiedExposureRecord),
    (runExactPlainRom transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
        (hidden, answers)).trace = prior ++ record :: later →
    WaitingControllerPrefixUnmarked transitionFuel
      (typedRestoredChallengeExposureStartsHere transitionFuel
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
          Payload Witness) (.challenge .gamma)
        (base.machine.blackBox.start hidden base.machine.observation)
        base.machine.environment base.restorationConfiguration)
      (exactRestoredGammaInitialState transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
        hidden) prior →
    RestoredGammaPrefixActivated transitionFuel
      (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
      hidden prior →
    extractedWidth29InitialWords k13.certificate.classified.k12.words =
      lanesFromPrefix hidden prior

/-- A pointwise production projection plus the causal residual-prefix theorem
constructs the exact pairwise functional consumed by K1.4. -/
noncomputable def
    ExactTag73GammaRestoredK14PreActivationLaneSource.toInitialLaneFunctional
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {canonicalDriverFuel transitionFuel : Nat}
    {base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {rounds : Nat}
    {extractor : ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
      Payload Witness}
    {withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap}
    {adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor
          withinForkCap)}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (source : ExactTag73GammaRestoredK14PreActivationLaneSource
      canonicalDriverFuel transitionFuel base rounds extractor withinForkCap
      adequate projection fixedInstance decoder clean) :
    ExactTag73GammaRestoredK14InitialLaneFunctional transitionFuel
      (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
      projection fixedInstance decoder clean where
  defaultLanes := source.defaultLanes
  defaultResponse := source.defaultResponse
  decoderAt := source.decoderAt
  sameInitialLanes := by
    intro hidden residual left right
    obtain ⟨prior, leftLater, firstRecord, rightRemaining, rightTail,
        leftTrace, unmarked, activated, rightPrefix, rightTrace⟩ :=
      root_sweep_gamma_fibre_replays_common_pre_activation_records base rounds
        source.roundsPositive extractor withinForkCap adequate projection
        fixedInstance hidden left.answers right.answers left.input
        (source.namedCompleteAt hidden left.answers left.cleanMember left.input)
        (left.residualExact.trans right.residualExact.symm)
    have leftLength := exact_plain_rom_trace_length transitionFuel
      (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
      (hidden, left.answers)
    have rightLength := run_unified_exposure_trace_length_exact transitionFuel
      (exactCompilerTargetCaps parameters).length
      (exactPlainRomCursor
        (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
        hidden).erase right.answers
    have capLength : (exactCompilerTargetCaps parameters).length =
        unifiedFull256ExposureCap parameters :=
      exact_compiler_target_caps_length parameters
    rw [leftTrace] at leftLength
    rw [rightTrace] at rightLength
    have rightTailNonempty : rightTail ≠ [] := by
      intro empty
      rw [empty] at rightLength
      simp only [List.length_append, List.length_nil, Nat.add_zero] at rightLength
      simp only [List.length_append, List.length_cons] at leftLength
      omega
    obtain ⟨rightRecord, rightLater, rightTailExact⟩ :=
      List.exists_cons_of_ne_nil rightTailNonempty
    have rightPlainTrace :
        (runExactPlainRom transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
          (hidden, right.answers)).trace =
            prior ++ rightRecord :: rightLater := by
      have rightErased :
          runUnifiedExposureTrace transitionFuel
              (exactCompilerTargetCaps parameters).length
              (exactPlainRomCursor
                (exactRootSweepWitnessConfiguration base rounds extractor
                  withinForkCap) hidden).erase right.answers =
            prior ++ rightRecord :: rightLater := by
        simpa only [rightTailExact] using rightTrace
      exact (exact_plain_rom_trace_is_erased_exposure_trace transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
        (hidden, right.answers)).trans rightErased
    have leftLanes := source.lanesAtPrefix hidden left.answers left.cleanMember
      left.input left.k13 left.failure prior leftLater firstRecord leftTrace
      unmarked activated
    have rightLanes := source.lanesAtPrefix hidden right.answers right.cleanMember
      right.input right.k13 right.failure prior rightLater rightRecord
      rightPlainTrace unmarked activated
    exact leftLanes.trans rightLanes.symm

/-- Release-facing K1.4 closure from the single pointwise production
projection.  All pairwise fibre functionality and the fixed degree-28 bad
challenge family are constructed inside Lean. -/
theorem exact_gamma_restored_k14_probability_le_of_pre_activation_lane_source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {canonicalDriverFuel transitionFuel : Nat}
    {base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {rounds : Nat}
    {extractor : ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
      Payload Witness}
    {withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap}
    {adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor
          withinForkCap)}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (source : ExactTag73GammaRestoredK14PreActivationLaneSource
      canonicalDriverFuel transitionFuel base rounds extractor withinForkCap
      adequate projection fixedInstance decoder clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73GammaRestoredOperationalK14Width29Event
          transitionFuel
            (exactRootSweepWitnessConfiguration base rounds extractor
              withinForkCap)
            projection fixedInstance decoder) ≤
      exactK14IdealRawError := by
  let functional := source.toInitialLaneFunctional
  let alignment := functional.toInitialLaneAlignment
  exact exact_gamma_restored_k14_probability_le_of_initial_lane_alignment
    hiddenLaw clean initialEncoderExact alignment

#print axioms ExactTag73GammaRestoredK14PreActivationLaneSource
#print axioms
  ExactTag73GammaRestoredK14PreActivationLaneSource.toInitialLaneFunctional
#print axioms
  exact_gamma_restored_k14_probability_le_of_pre_activation_lane_source

end
end AspisK1.V7Tag73GammaRestoredK14PreActivationLaneSource
