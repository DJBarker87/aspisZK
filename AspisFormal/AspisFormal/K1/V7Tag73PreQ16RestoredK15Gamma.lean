import AspisFormal.K1.V7Tag73ExactCausalK15Reduction
import AspisFormal.K1.V7Tag73PreQ16RestoredK15Context

/-! # Corrected pre-q16 constrained-gamma endpoint -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73PreQ16RestoredK15Gamma

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCausalK15Reduction
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73PreQ16OperationalK15Stage
open AspisK1.V7Tag73PreQ16OperationalRelationSourceFacts
open AspisK1.V7Tag73PreQ16RestoredK15Context
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7CombinedCandidateExact
open AspisPool.V7CorrelatedPointClaimExtraction
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7PointClaimBatchBinding
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar
open AspisV6Width29ConstrainedFunctionalExtraction
open AspisV6Width29CorrelatedAgreement

noncomputable section

/-- Small non-dependent name for the constrained restored-gamma proposition.
Keeping the operational context out of this head symbol prevents downstream
event proofs from normalizing the full scheduler/material tower merely to match
the theorem conclusion. -/
def ExactPreQ16ConstrainedGammaStatement
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (point : Fin 10 → QM31Exact)
    (fields : FixedFieldView QM31Exact)
    (family : RestoredSelectedChainFamily decoder words)
    (gamma : QM31Exact) : Prop :=
  gamma ∈ acceptedRestoredPointConstrainedGammaSet decoder words point
    fields.pointClaim family

/-- A corrected material value with all causal predecessors clear lies in the
single restoration-wide constrained gamma set. -/
theorem preQ16_gamma_branch_mem_constrained
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {basis : Basis (Fin 4) F QM31Exact} {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (environment : ExactPreQ16RestoredK15Environment transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon)
    (context : ExactPreQ16K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding)
    (predecessors : ExactPreQ16GammaPredecessors environment context) :
    ExactPreQ16ConstrainedGammaStatement decoder context.k13.words
      (context.run environment.operational).point
      (context.fields environment.operational) (environment.family context)
      (exactK13ParsedProof context.input).gamma := by
  unfold ExactPreQ16ConstrainedGammaStatement
  let material := context.material environment.operational
  let family := environment.family context
  let fields := context.fields environment.operational
  let transcript := context.run environment.operational
  have positive := positive_relation_facts_of_parsed_source_bindings
    material.source.sourceBinding material.source.finalSource
    (exactTag73K13AuthenticatedQueryVector decoder context.input context.k12)
    material.source.querySource.toOperationalSourceBinding
    material.authenticatedQueryValuesExact material.data.terminalSource
  have aggregateExact :
      claimedPointBatch fields (exactK13ParsedProof context.input).gamma
          (exactOperationalChallenge context.input .kappa) =
        extractedPointBatch context.k14.parsed.extraction transcript.point
          (exactOperationalChallenge context.input .kappa) := by
    exact (relation_and_point_aggregate_exact_outside_relation_collisions
      material.data.masks fields context.k14.parsed.extraction transcript.point
      (exactOperationalChallenge context.input .kappa) material.data.execution
      material.source.initialEncoderEq
      material.source.finalSource.initialValuesExact
      material.source.executionInitialWeights
      material.source.executionInitialClaim material.source.inactiveExact
      positive.1 positive.2.1 positive.2.2 predecessors.noOod
      predecessors.noAlpha).2.2.2
  have everyRowZero :=
    every_row_gamma_discrepancy_zero_of_aggregate_exact fields
      context.k14.parsed.extraction transcript.point
      (exactOperationalChallenge context.input .kappa) aggregateExact
      predecessors.noKappa
  have familyAvailable := environment.familyAvailable context
  have familySelected := environment.familySelected context
  have responseAt := family.responseAt (exactK13ParsedProof context.input).gamma
    familyAvailable
  have selectedValid := selected_chain_yields_valid_width29_response decoder
    context.k13.words (exactK13ParsedProof context.input).gamma
    (exactK13ParsedProof context.input).disclosedFinal
    (exactK13ParsedProof context.input).schedule
    context.k14.parsed.extraction.combined
    context.k14.parsed.extraction.combinedSelected
  have acceptedSupportEqRestored :=
    accepted_restored_support_eq_restored_of_available decoder context.k13.words
      family (exactK13ParsedProof context.input).gamma familyAvailable
  have restoredSupportEqSelected :=
    restoredWidth29Strategy_support_eq_selected decoder
      (extractedWidth29InitialWords context.k13.words)
      (family.selected (exactK13ParsedProof context.input).gamma) family.response
      (exactK13ParsedProof context.input).gamma responseAt
  have acceptedSupportEqSelected :
      (acceptedRestoredWidth29Strategy decoder context.k13.words family).support
          (exactK13ParsedProof context.input).gamma =
        (selectedCandidateStrategy decoder
          (extractedWidth29InitialWords context.k13.words)
          context.k14.parsed.extraction.combined).support
            (exactK13ParsedProof context.input).gamma := by
    rw [acceptedSupportEqRestored, restoredSupportEqSelected,
      familySelected]
  have acceptedValid : Width29ValidResponse exactInitialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords context.k13.words)
      (acceptedRestoredWidth29Strategy decoder context.k13.words family)
      (exactK13ParsedProof context.input).gamma := by
    constructor
    · rw [acceptedSupportEqSelected]
      exact selectedValid.1
    · intro index member
      have selectedMember : index ∈
          (selectedCandidateStrategy decoder
            (extractedWidth29InitialWords context.k13.words)
            context.k14.parsed.extraction.combined).support
              (exactK13ParsedProof context.input).gamma := by
        rw [← acceptedSupportEqSelected]
        exact member
      have selectedAgreement := selectedValid.2 index selectedMember
      change width29CurveValue (extractedWidth29InitialWords context.k13.words)
          (exactK13ParsedProof context.input).gamma index =
        exactInitialEncoder
          (family.response (exactK13ParsedProof context.input).gamma) index
      rw [responseAt, familySelected, ← material.source.initialEncoderEq]
      exact selectedAgreement
  have functionalConstraint : Width29FunctionalConstraint
      (pointFunctional transcript.point) fields.pointClaim
      (acceptedRestoredWidth29Strategy decoder context.k13.words family)
      (exactK13ParsedProof context.input).gamma := by
    intro row
    have rowZero : rowGammaDiscrepancy fields context.k14.parsed.extraction
        transcript.point row = 0 := congrFun everyRowZero row
    have rowBatchExact :=
      (rowGammaDiscrepancy_eq_zero_iff fields context.k14.parsed.extraction
        transcript.point row).mp rowZero
    calc
      pointFunctional transcript.point row
          ((acceptedRestoredWidth29Strategy decoder context.k13.words family).candidate
            (exactK13ParsedProof context.input).gamma) =
        pointFunctional transcript.point row
          (family.response (exactK13ParsedProof context.input).gamma) := by rfl
      _ = pointFunctional transcript.point row
          (family.selected (exactK13ParsedProof context.input).gamma).1 := by
        rw [responseAt]
      _ = pointFunctional transcript.point row
          context.k14.parsed.extraction.combined.1 := by rw [familySelected]
      _ = pointFunctional transcript.point row
          (batchInitialMessages context.k14.parsed.extraction.components
            (exactK13ParsedProof context.input).gamma) := by
        rw [CoherentTraceExtraction.combined_eq_batchInitialMessages
          context.k14.parsed.extraction material.source.initialEncoderEq]
      _ = width29Batch
          (fun lane ↦ componentPointClaim context.k14.parsed.extraction
            transcript.point row lane) (exactK13ParsedProof context.input).gamma :=
        pointFunctional_batchInitialMessages transcript.point row
          context.k14.parsed.extraction.components
          (exactK13ParsedProof context.input).gamma
      _ = width29Batch (fields.pointClaim row)
          (exactK13ParsedProof context.input).gamma := rowBatchExact.symm
  have functionalConstraintRaw : Width29FunctionalConstraint
      (pointFunctional (context.run environment.operational).point)
      (context.fields environment.operational).pointClaim
      (acceptedRestoredWidth29Strategy decoder context.k13.words family)
      (exactK13ParsedProof context.input).gamma := by
    simpa only [fields, transcript] using functionalConstraint
  unfold acceptedRestoredPointConstrainedGammaSet
  rw [mem_width29GoodChallenges_iff]
  refine ⟨exact_parsed_gamma_ne_zero material.source.sourceBinding, ?_⟩
  constructor
  · simpa [family, constrainedWidth29Strategy, functionalConstraintRaw] using
      acceptedValid.1
  · intro index member
    have acceptedMember : index ∈
        (acceptedRestoredWidth29Strategy decoder context.k13.words family).support
          (exactK13ParsedProof context.input).gamma := by
      simpa [family, constrainedWidth29Strategy, functionalConstraintRaw] using member
    simpa [family, constrainedWidth29Strategy, functionalConstraintRaw] using
      acceptedValid.2 index acceptedMember

#print axioms preQ16_gamma_branch_mem_constrained

end

end AspisK1.V7Tag73PreQ16RestoredK15Gamma
