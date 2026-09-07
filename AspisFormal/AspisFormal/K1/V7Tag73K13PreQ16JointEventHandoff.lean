import AspisFormal.K1.V7Tag73K13PreQ16QueryHandoff
import AspisFormal.K1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
import AspisFormal.K1.V7Tag73K13PreQ16TargetProbability

/-!
# Corrected pre-q16 K1.3 joint-event handoff

This replaces the old joint witness whose consistency set was computed from
the completed prover history.  The bad set below is computed from the literal
root-record prefix before the selected final-work/q16 coordinate.  Its size and
membership come from the re-run classifier, while the final-work and q16
coordinates remain the already checked operational realization.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13PreQ16JointEventHandoff

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerQ16EventHandoff
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K13PreQ16QueryHandoff
open AspisK1.V7Tag73K13PreQ16TargetProbability
open AspisK1.V7Tag73K13PreQ16ViewAgreement
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction
open AspisV6QueryBatchSoundness

noncomputable section

/-- Proof-relevant membership in one genuine corrected K1.3 q16 trial. -/
structure ExactPreQ16K13JointTrialWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (sample : ExactCompilerSample HiddenTape parameters)
    (trial : ExactCompilerExposureTrial parameters) : Type where
  input : ExactK12OperationalInput transitionFuel configuration projection
    fixedInstance sample
  prior : List UnifiedExposureRecord
  later : List UnifiedExposureRecord
  pivotActor : QueryActor
  pivotInput : ShaInput
  pivotAnswer : Digest256
  rootExact : exactFixedRootRecords input.package.root =
    prior ++ (.machineFresh pivotActor pivotInput pivotAnswer :
      UnifiedExposureRecord) :: later
  trialExact : trial.val = prior.length
  bad : Finset (Fin 262144)
  badExact : bad = exactPreQ16K13Bad decoder input prior
  badCard : bad.card ≤ 9557
  allBad : AllInBad bad
    (semanticScheduleOfOperational
      (exactOperationalTape input).search.selectedSchedule)
  actualTrial : ExactFixedK13ActualJointTrial input trial
  coordinate :
    exactFixedK13TrialCoordinates transitionFuel configuration trial sample ∈
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun _residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulBadEvent bad)

/-- One corrected chronological q16 trial event. -/
def exactPreQ16K13JointTrialEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | Nonempty (ExactPreQ16K13JointTrialWitness transitionFuel
    configuration projection fixedInstance decoder sample trial)}

/-- Every actual selected final-work/q16 trial exposes the exact chronological
prefix used by the corrected word. -/
theorem actual_joint_trial_has_preQ16_anchor
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input trial) :
    ∃ prior later pivotActor pivotInput pivotAnswer,
      exactFixedRootRecords input.package.root =
        prior ++ (.machineFresh pivotActor pivotInput pivotAnswer :
          UnifiedExposureRecord) :: later ∧
      trial.val = prior.length := by
  rcases exact_fixed_k13_actual_joint_trial_anchor_actor_cases input trial actual
      with verifier | adversary
  · rcases verifier with ⟨prior, later, target, answer, rootExact, trialExact⟩
    exact ⟨prior, later, .verifier, target, answer, rootExact, trialExact⟩
  · rcases adversary with ⟨prior, later, target, answer, rootExact, trialExact⟩
    exact ⟨prior, later, .adversary, target, answer, rootExact, trialExact⟩

/-- Package a corrected small-set branch into the exact final-work/q16 event
already consumed by the probability theorem. -/
theorem preQ16_query_failure_has_joint_trial_witness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input trial)
    (prior later : List UnifiedExposureRecord)
    (pivotActor : QueryActor) (pivotInput : ShaInput) (pivotAnswer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh pivotActor pivotInput pivotAnswer :
        UnifiedExposureRecord) :: later)
    (trialExact : trial.val = prior.length)
    (decoded : Fin 641 → QM31Exact)
    (source : ExactParsedProofSourceBinding input decoded)
    (failure : QueryPhaseFailure (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder)
      (parsedK13Transcript
        (preQ16PrefixWords prior (exactK12Roots input))
        (exactK13ParsedProof input))
      (exactK13ParsedProof input).queries) :
    Nonempty (ExactPreQ16K13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder sample trial) := by
  let bad := exactPreQ16K13Bad decoder input prior
  obtain ⟨badCard, allBad⟩ :=
    preQ16_query_failure_exposes_literal_q16_bad_set input prior decoded source
      failure
  have actualCopy := actual
  obtain ⟨_digest, _workAnswer, _base, workAccepted, _prefinal, _baseExact,
      _pairLabeled, _workLabeled, workCoordinate, realized⟩ := actualCopy
  have q16Success :=
    operational_realization_implies_q16_digest_forest_succeeds realized
  have q16Bad : successfulQ16DigestForestEquiv
        ⟨(exactFixedK13TrialCoordinates transitionFuel configuration trial
          sample).2.2, q16Success⟩ ∈
      q16SuccessfulCoordinatesBadEvent bad := by
    apply operational_all_in_bad_implies_successful_coordinate_bad realized bad
    exact allBad
  refine ⟨{
    input := input
    prior := prior
    later := later
    pivotActor := pivotActor
    pivotInput := pivotInput
    pivotAnswer := pivotAnswer
    rootExact := rootExact
    trialExact := trialExact
    bad := bad
    badExact := rfl
    badCard := badCard
    allBad := allBad
    actualTrial := actual
    coordinate := ?_ }⟩
  refine ⟨q16Success, ?_⟩
  change FinalWork34Accepted
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        sample).2.1 ∧
    successfulQ16DigestForestEquiv
        ⟨(exactFixedK13TrialCoordinates transitionFuel configuration trial
          sample).2.2, q16Success⟩ ∈
      q16SuccessfulCoordinatesBadEvent bad
  exact ⟨workCoordinate ▸ workAccepted, q16Bad⟩

/-- Pointwise accepted-run decomposition used by the corrected probability
wrapper.  Every branch is either a pre-q16 K1.3 object or an already named
Merkle event; no completed-prover bad set remains. -/
theorem accepted_input_classifies_through_preQ16_trial
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (decoded : Fin 641 → QM31Exact)
    (source : ExactParsedProofSourceBinding input decoded)
    (positions : ExactOpeningPositionsSourceBinding input)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (accepts : IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    (∃ trial : ExactCompilerExposureTrial parameters,
      Nonempty (ExactPreQ16K13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder sample trial)) ∨
    (∃ (trial : ExactCompilerExposureTrial parameters)
        (prior : List UnifiedExposureRecord),
      Nonempty (ParsedK13Certificate decoder
        (preQ16PrefixWords prior (exactK12Roots input))
        (exactK13ParsedProof input))) ∨
    (∃ (trial : ExactCompilerExposureTrial parameters)
        (prior : List UnifiedExposureRecord),
      OneFoldReductionFailure (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder)
        (parsedK13Transcript
          (preQ16PrefixWords prior (exactK12Roots input))
          (exactK13ParsedProof input))) ∨
    sample ∈ exactK13PreQ16LateTargetEvent transitionFuel configuration
      projection fixedInstance ∨
    RawLogTruncatedDigestCollision (exactK12Truncate input)
      (exactK12OrderedQueries input) := by
  obtain ⟨digest, workAnswer, base, trial, workAccepted, prefinalOrigin,
      baseExact, pairLabeled, workLabeled, workCoordinate, realized⟩ :=
    exact_compiler_accepted_dag_q16_operational_realization transitionRoom
      programmedCover input frontierExact
  let actual : ExactFixedK13ActualJointTrial input trial :=
    ⟨digest, workAnswer, base, workAccepted, prefinalOrigin, baseExact,
      pairLabeled, workLabeled, workCoordinate, realized⟩
  obtain ⟨prior, later, pivotActor, pivotInput, pivotAnswer, rootExact,
      trialExact⟩ := actual_joint_trial_has_preQ16_anchor input trial actual
  rcases exact_preQ16_k13_classification_or_counted_merkle_failure
      initialEncoderExact input k12 decoded source positions prior later
        (.machineFresh pivotActor pivotInput pivotAnswer) rootExact accepts with
    classified | lateOrCollision
  · rcases classified with certificate | queryOrFold
    · exact Or.inr (Or.inl ⟨trial, prior, certificate⟩)
    · rcases queryOrFold with queryFailure | foldFailure
      · exact Or.inl ⟨trial,
          preQ16_query_failure_has_joint_trial_witness input trial actual prior
            later pivotActor pivotInput pivotAnswer rootExact trialExact decoded
              source queryFailure⟩
      · exact Or.inr (Or.inr (Or.inl ⟨trial, prior, foldFailure⟩))
  · rcases lateOrCollision with late | collision
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨input, trial, prior, later,
          pivotActor, pivotInput, pivotAnswer, actual, rootExact, trialExact,
          late⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr collision)))

/-! ## Proof-relevant corrected stage handoff -/

/-- The complete chronological anchor retained by the corrected K1.3 stage.
Unlike the earlier disjunctive cover, this record does not discard the
actual selected final-work trial or its literal root-record split when the
pre-q16 classifier succeeds. -/
structure ExactPreQ16K13ChronologicalAnchor
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  trial : ExactCompilerExposureTrial parameters
  actual : ExactFixedK13ActualJointTrial input trial
  prior : List UnifiedExposureRecord
  later : List UnifiedExposureRecord
  pivotActor : QueryActor
  pivotInput : ShaInput
  pivotAnswer : Digest256
  rootExact : exactFixedRootRecords input.package.root =
    prior ++ (.machineFresh pivotActor pivotInput pivotAnswer :
      UnifiedExposureRecord) :: later
  trialExact : trial.val = prior.length

/-- Successful corrected K1.3 data on the word fixed immediately before the
selected final-work/q16 coordinate.  This is the object K1.4 and K1.5 must
consume; the later completed-prover word is intentionally absent. -/
structure ExactPreQ16K13StageCertificate
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  anchor : ExactPreQ16K13ChronologicalAnchor input
  words : AspisPool.V7MerkleQueryExtractor.ExtractedWords
  wordsExact : words =
    preQ16PrefixWords anchor.prior (exactK12Roots input)
  projections : disclosuresAreProjections words (exactK12Openings input)
  parsed : ParsedK13Certificate decoder words (exactK13ParsedProof input)

/-- The corrected one-fold branch retains the same complete chronological
anchor as success.  It can therefore be bounded against the actual fold
challenge without reconstructing a post-q16 history. -/
structure ExactPreQ16K13StageOneFoldFailure
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  anchor : ExactPreQ16K13ChronologicalAnchor input
  words : AspisPool.V7MerkleQueryExtractor.ExtractedWords
  wordsExact : words =
    preQ16PrefixWords anchor.prior (exactK12Roots input)
  failure : OneFoldReductionFailure (exactK13ParsedProof input).schedule
    (exactK13Encoders decoder)
    (parsedK13Transcript words (exactK13ParsedProof input))

/-- Every non-success outcome of the corrected accepted-input classifier is
one already named event: the q16 small-set trial, the pre-q16 one-fold
failure, the adaptive late-target event, or the existing 208-bit collision.
There is no opaque catch-all constructor. -/
inductive ExactPreQ16K13StageError
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input) : Type
  | idealRejected :
      ¬ IdealAccepts (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder)
        (exactK13Transcript input k12)
        (exactK13ParsedProof input).queries →
      ExactPreQ16K13StageError decoder input k12
  | q16 {trial : ExactCompilerExposureTrial parameters} :
      ExactPreQ16K13JointTrialWitness transitionFuel configuration projection
        fixedInstance decoder sample trial →
      ExactPreQ16K13StageError decoder input k12
  | oneFold : ExactPreQ16K13StageOneFoldFailure decoder input →
      ExactPreQ16K13StageError decoder input k12
  | lateTarget : sample ∈ exactK13PreQ16LateTargetEvent transitionFuel
      configuration projection fixedInstance →
      ExactPreQ16K13StageError decoder input k12
  | collision : RawLogTruncatedDigestCollision (exactK12Truncate input)
      (exactK12OrderedQueries input) →
      ExactPreQ16K13StageError decoder input k12

/-- Strong proof-relevant version of
`accepted_input_classifies_through_preQ16_trial`.  The successful and
one-fold branches retain the actual chronological anchor instead of merely
existentially naming an unrelated trial and prefix. -/
theorem accepted_input_has_preQ16_stage_certificate_or_error
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (decoded : Fin 641 → QM31Exact)
    (source : ExactParsedProofSourceBinding input decoded)
    (positions : ExactOpeningPositionsSourceBinding input)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (accepts : IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    Nonempty (ExactPreQ16K13StageCertificate decoder input) ∨
      Nonempty (ExactPreQ16K13StageError decoder input k12) := by
  obtain ⟨digest, workAnswer, base, trial, workAccepted, prefinalOrigin,
      baseExact, pairLabeled, workLabeled, workCoordinate, realized⟩ :=
    exact_compiler_accepted_dag_q16_operational_realization transitionRoom
      programmedCover input frontierExact
  let actual : ExactFixedK13ActualJointTrial input trial :=
    ⟨digest, workAnswer, base, workAccepted, prefinalOrigin, baseExact,
      pairLabeled, workLabeled, workCoordinate, realized⟩
  obtain ⟨prior, later, pivotActor, pivotInput, pivotAnswer, rootExact,
      trialExact⟩ := actual_joint_trial_has_preQ16_anchor input trial actual
  let anchor : ExactPreQ16K13ChronologicalAnchor input :=
    ⟨trial, actual, prior, later, pivotActor, pivotInput, pivotAnswer,
      rootExact, trialExact⟩
  rcases exact_preQ16_k13_classification_or_counted_merkle_failure
      initialEncoderExact input k12 decoded source positions prior later
        (.machineFresh pivotActor pivotInput pivotAnswer) rootExact accepts with
    classified | lateOrCollision
  · rcases classified with certificate | queryOrFold
    · rcases exact_accepted_openings_yield_preQ16_projections_or_counted_failure
          input prior later
            (.machineFresh pivotActor pivotInput pivotAnswer) rootExact
            k12.openingsAccepted k12.suppliedCovered with
        projections | late | collision
      · exact Or.inl ⟨anchor,
          preQ16PrefixWords prior (exactK12Roots input), rfl, projections,
          Classical.choice certificate⟩
      · exact Or.inr ⟨.lateTarget ⟨input, trial, prior, later,
          pivotActor, pivotInput, pivotAnswer, actual, rootExact, trialExact,
          late⟩⟩
      · exact Or.inr ⟨.collision collision⟩
    · rcases queryOrFold with queryFailure | foldFailure
      · exact Or.inr ⟨.q16
          (Classical.choice
            (preQ16_query_failure_has_joint_trial_witness input trial actual
              prior later pivotActor pivotInput pivotAnswer rootExact trialExact
              decoded source queryFailure))⟩
      · exact Or.inr ⟨.oneFold ⟨anchor,
          preQ16PrefixWords prior (exactK12Roots input), rfl, foldFailure⟩⟩
  · rcases lateOrCollision with late | collision
    · exact Or.inr ⟨.lateTarget ⟨input, trial, prior, later, pivotActor,
        pivotInput, pivotAnswer, actual, rootExact, trialExact, late⟩⟩
    · exact Or.inr ⟨.collision collision⟩

/-- Data-valued total classifier obtained from the proposition-valued strong
cover.  `Classical.choice` only eliminates proof data into the dependent
stage sum; it adds no axiom beyond Lean's standard classical basis. -/
noncomputable def classifyAcceptedInputThroughPreQ16Stage
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (decoded : Fin 641 → QM31Exact)
    (source : ExactParsedProofSourceBinding input decoded)
    (positions : ExactOpeningPositionsSourceBinding input)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (accepts : IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    ExactPreQ16K13StageCertificate decoder input ⊕
      ExactPreQ16K13StageError decoder input k12 :=
  Classical.choice <| by
    rcases accepted_input_has_preQ16_stage_certificate_or_error
        transitionRoom programmedCover initialEncoderExact input k12 decoded
        source positions frontierExact accepts with success | failure
    · exact success.map Sum.inl
    · exact failure.map Sum.inr

/-- Total corrected K1.3 classifier for one authenticated K1.2 input.  The
only extra branch is literal rejection of the completed accepted transcript;
all accepting executions are reclassified on the chronological pre-q16 word.
-/
noncomputable def classifyInputThroughPreQ16Stage
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (decoded : Fin 641 → QM31Exact)
    (source : ExactParsedProofSourceBinding input decoded)
    (positions : ExactOpeningPositionsSourceBinding input)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    ExactPreQ16K13StageCertificate decoder input ⊕
      (ExactK13Error decoder input k12 ⊕
        ExactPreQ16K13StageError decoder input k12) := by
  classical
  by_cases accepts : IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries
  · exact (classifyAcceptedInputThroughPreQ16Stage transitionRoom
      programmedCover initialEncoderExact input k12 decoded source positions
      frontierExact accepts).map id Sum.inr
  · exact .inr (.inl (.idealRejected accepts))

/-! ## K1.4 on the same corrected word -/

/-- Coherent-chain extraction on exactly the word retained by corrected K1.3.
The certificate is indexed by the K1.3 object, so downstream code cannot
substitute the later completed-prover word. -/
structure ExactPreQ16K14StageCertificate
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k13 : ExactPreQ16K13StageCertificate decoder input) : Type where
  parsed : ParsedK14Certificate decoder binding k13.words
    (exactK13ParsedProof input)

/-- The sole K1.4 failure on the corrected K1.3 word. -/
structure ExactPreQ16K14StageError
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k13 : ExactPreQ16K13StageCertificate decoder input) : Type where
  parsed : ParsedK14Error decoder k13.words (exactK13ParsedProof input)

/-- Total width-29 classifier, run on the same pre-q16 word carried by K1.3.
-/
noncomputable def classifyPreQ16K14Stage
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k13 : ExactPreQ16K13StageCertificate decoder input) :
    ExactPreQ16K14StageCertificate decoder binding input k13 ⊕
      ExactPreQ16K14StageError decoder input k13 :=
  match classifyParsedK14 decoder binding k13.words
      (exactK13ParsedProof input) k13.parsed with
  | .inl certificate => .inl ⟨certificate⟩
  | .inr error => .inr ⟨error⟩

/-! ## Exact authenticated-vector transport -/

/-- The sixteen once-folded values read from an arbitrary parser-data word.
-/
def parsedK13AuthenticatedQueryVector
    (words : ExtractedWords) (proof : Tag73K12ParsedProof) :
    QueryVector QM31Exact :=
  fun ordinal =>
    circleFoldLayer 262144 proof.schedule.alpha proof.schedule.circleInv2x
      proof.schedule.circleInv2y (parsedK13Transcript words proof).initial
      (proof.queries ordinal)

/-- Two words which project the same paired opening have the same once-folded
value at that opening's position. -/
theorem circleFoldLayer_eq_of_shared_projected_opening
    (schedule : OneFoldSchedule M31Exact QM31Exact)
    (left right : ExtractedWords) (opening : PairedOpening)
    (leftProjection : openingIsProjection left opening)
    (rightProjection : openingIsProjection right opening)
    (gamma : QM31Exact) (disclosedFinal : FinalMessage QM31Exact)
    (query : Fin 262144)
    (positionExact : query.val = opening.position.val) :
    circleFoldLayer 262144 schedule.alpha schedule.circleInv2x
        schedule.circleInv2y
        (extractedIdealTranscript left gamma disclosedFinal).initial query =
      circleFoldLayer 262144 schedule.alpha schedule.circleInv2x
        schedule.circleInv2y
        (extractedIdealTranscript right gamma disclosedFinal).initial query := by
  rw [circleFoldLayer_apply, circleFoldLayer_apply]
  apply congrArg
  funext slot
  have childExact : childIndex query slot =
      childIndex opening.position slot := by
    apply Fin.ext
    simp only [childIndex_val]
    omega
  rw [childExact]
  exact projected_opening_batched_fibre_eq left right opening leftProjection
    rightProjection gamma slot

theorem parsedK13AuthenticatedQueryVector_eq_of_shared_projections
    (left right : ExtractedWords) (proof : Tag73K12ParsedProof)
    (openings : Fin 16 → PairedOpening)
    (leftProjection : disclosuresAreProjections left openings)
    (rightProjection : disclosuresAreProjections right openings)
    (positions : ∀ ordinal,
      (proof.queries ordinal).val = (openings ordinal).position.val) :
    parsedK13AuthenticatedQueryVector left proof =
      parsedK13AuthenticatedQueryVector right proof := by
  funext ordinal
  simpa [parsedK13AuthenticatedQueryVector, parsedK13Transcript] using
    circleFoldLayer_eq_of_shared_projected_opening proof.schedule left right
      (openings ordinal) (leftProjection ordinal) (rightProjection ordinal)
      proof.gamma proof.disclosedFinal (proof.queries ordinal)
      (positions ordinal)

set_option maxHeartbeats 1000000 in
/-- The corrected pre-q16 word and the established K1.2 word yield exactly
the same authenticated q16 vector because both project the literal accepted
paired openings at the source-bound selected positions. -/
theorem ExactPreQ16K13StageCertificate.authenticatedQueryVector_eq_exact
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {decoded : Fin 641 → QM31Exact}
    (certificate : ExactPreQ16K13StageCertificate decoder input)
    (k12 : ExactPrefixK12Certificate input)
    (parsedSource : ExactParsedProofSourceBinding input decoded)
    (positions : ExactOpeningPositionsSourceBinding input) :
    parsedK13AuthenticatedQueryVector certificate.words
        (exactK13ParsedProof input) =
      exactTag73K13AuthenticatedQueryVector decoder input k12 := by
  have positionsExact : ∀ ordinal,
      ((exactK13ParsedProof input).queries ordinal).val =
        (exactK12Openings input ordinal).position.val := by
    intro ordinal
    rw [parsedSource.selectedQueriesExact]
    exact (positions ordinal).symm
  calc
    parsedK13AuthenticatedQueryVector certificate.words
        (exactK13ParsedProof input) =
        parsedK13AuthenticatedQueryVector k12.words
          (exactK13ParsedProof input) :=
      parsedK13AuthenticatedQueryVector_eq_of_shared_projections
        certificate.words k12.words (exactK13ParsedProof input)
        (exactK12Openings input) certificate.projections k12.projections
        positionsExact
    _ = exactTag73K13AuthenticatedQueryVector decoder input k12 := rfl

#print axioms preQ16_query_failure_has_joint_trial_witness
#print axioms actual_joint_trial_has_preQ16_anchor
#print axioms accepted_input_classifies_through_preQ16_trial
#print axioms accepted_input_has_preQ16_stage_certificate_or_error
#print axioms classifyAcceptedInputThroughPreQ16Stage
#print axioms classifyInputThroughPreQ16Stage
#print axioms classifyPreQ16K14Stage
#print axioms circleFoldLayer_eq_of_shared_projected_opening
#print axioms parsedK13AuthenticatedQueryVector_eq_of_shared_projections
#print axioms ExactPreQ16K13StageCertificate.authenticatedQueryVector_eq_exact

end


end AspisK1.V7Tag73K13PreQ16JointEventHandoff
