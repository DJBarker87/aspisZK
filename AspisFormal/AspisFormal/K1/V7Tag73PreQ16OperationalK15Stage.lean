import AspisFormal.K1.V7Tag73PreQ16OperationalRelationSourceFacts
import AspisFormal.K1.V7Tag73ExactOperationalK15Stage

/-!
# Corrected pre-q16 operational K1.5 stage

This module reconnects the existing production K1.5 data to the coherent
trace extracted from the chronological pre-q16 word.  The production query
callback remains unchanged: the preceding module proves that its established
K1.2 authenticated vector is identical to the corrected word's vector.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16OperationalK15Stage

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73BatchedQuerySourceBridge
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16QueryHandoff
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73OperationalRelationSourceFacts
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73PreQ16OperationalRelationSourceFacts
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedDeployedCopyLaneCapstone
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7InactiveClaimBinding
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PoseidonRowsFromTrace
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7Tag73InactiveHelperAggregate
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5SumcheckTranscriptBinding
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar

noncomputable section

/-- The exact operational table with the corrected coherent extraction. -/
def exactTag73PreQ16OperationalTable
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k13 : ExactPreQ16K13StageCertificate decoder input}
    (k14 : ExactPreQ16K14StageCertificate decoder decoderBinding input k13)
    (basis : Basis (Fin 4) F QM31Exact) (rc : RoundConstants)
    (data : ExactTag73OperationalK15Data input) : Fin 1024 → QM31Exact :=
  maskedOracle (operationalAcceptedRun input data.decoded data.fixedDecode).eta
    (extractedUnmaskedSemanticTable basis fixedInstance.statement
      k14.parsed.extraction
      (deployedPoseidonRows rc (extractedPhysicalTrace k14.parsed.extraction))
      (deployedCompiledCopyLane
        (concreteDeployedCopyRegistryProjection k14.parsed.extraction)
        (exactOperationalChallenge input .lambda)
        (exactOperationalChallenge input .chi) data.helper)
      (exactOperationalChallenge input .theta)
      (fun coordinate => exactOperationalChallenge input
        (.zerocheckPoint coordinate))
      (exactOperationalChallenge input .mu) data.helper)
    data.mask

/-- Literal source equalities for the corrected extraction.  The query source
continues to name the established K1.2 authenticated vector; its equality to
the corrected vector is proved below. -/
structure ExactPreQ16OperationalK15SourceBinding
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (k12 : ExactPrefixK12Certificate input)
    (k13 : ExactPreQ16K13StageCertificate decoder input)
    (k14 : ExactPreQ16K14StageCertificate decoder decoderBinding input k13)
    (basis : Basis (Fin 4) F QM31Exact) (rc : RoundConstants)
    (data : ExactTag73OperationalK15Data input) : Prop where
  sourceBinding : ExactParsedProofSourceBinding input data.decoded
  openingPositions : ExactOpeningPositionsSourceBinding input
  honestTableExact : data.honestTable =
    exactTag73PreQ16OperationalTable k14 basis rc data
  honestPointExact : data.honestPoint =
    (operationalAcceptedRun input data.decoded data.fixedDecode).point
  maskInitialExact : (operationalFixedFields data.decoded).initialClaim =
    tableSum data.mask
  terminalOpeningExact :
    semanticTerminalClaim (operationalFixedFields data.decoded)
        (operationalAcceptedRun input data.decoded data.fixedDecode).point =
      claimAtStep (tableSum
        (exactTag73PreQ16OperationalTable k14 basis rc data))
        (castFixedOracleTenRoundTrace data.honest honestTableExact
          honestPointExact).messages
        (operationalAcceptedRun input data.decoded data.fixedDecode).point
        (Fin.last 10)
  inactiveSumZero : DeployedCopyHelperInactiveSumZero data.helper
  initialEncoderEq : decoder.initialEncoder = exactInitialEncoder
  finalEncoderEq : decoder.finalEncoder = exactFinalEncoder
  executionInitialWeights : data.execution.initialWeights =
    extractedInitialRelationWeights data.masks
      (operationalAcceptedRun input data.decoded data.fixedDecode).point
      (exactOperationalChallenge input .kappa)
  executionInitialClaim : data.execution.initialClaim =
    relationClaimBeforeOod (operationalFixedFields data.decoded)
      (exactK13ParsedProof input).gamma
      (exactOperationalChallenge input .kappa)
  inactiveExact : (operationalFixedFields data.decoded).inactiveClaim =
    inactiveClaim data.masks k14.parsed.extraction.combined.1
  finalSource : ExactParsedFinal256ExecutionBinding input k13.words
    k14.parsed.extraction data.decoded data.execution
  querySource : ExactAuthenticatedQueryBatchSourceBinding data.execution
    (exactK13ParsedProof input).queries
    (exactOperationalChallenge input .queryBatch)
    (exactTag73K13AuthenticatedQueryVector decoder input k12)

/-- Complete per-run K1.5 material for corrected K1.3/K1.4. -/
structure ExactPreQ16OperationalK15Material
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k13 : ExactPreQ16K13StageCertificate decoder input)
    (k14 : ExactPreQ16K14StageCertificate decoder decoderBinding input k13)
    (basis : Basis (Fin 4) F QM31Exact) (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode) : Type where
  data : ExactTag73OperationalK15Data input
  source : ExactPreQ16OperationalK15SourceBinding k12 k13 k14 basis rc data
  clientExtractor : ExactPlainRomWitnessExtractor V5PublicStatement
    Tag73K12ParsedProof Payload DecodedSpendWitness
  clientReturned : input.package.root.full.clientRun.halt =
    .returned clientExtractor
  clientExtracts : clientExtractor
      input.package.root.full.clientRun.accumulator =
    some (decodeTag73SpendWitness fixedInstance.statement
      k14.parsed.extraction)

/-- Transport the honest ten-round trace to the corrected table and point. -/
def ExactPreQ16OperationalK15Material.exactHonest
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {k13 : ExactPreQ16K13StageCertificate decoder input}
    {k14 : ExactPreQ16K14StageCertificate decoder decoderBinding input k13}
    {basis : Basis (Fin 4) F QM31Exact} {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (material : ExactPreQ16OperationalK15Material input k12 k13 k14 basis rc
      poseidon) :
    FixedOracleTenRoundTrace
      (exactTag73PreQ16OperationalTable k14 basis rc material.data)
      (operationalAcceptedRun input material.data.decoded
        material.data.fixedDecode).point :=
  castFixedOracleTenRoundTrace material.data.honest
    material.source.honestTableExact material.source.honestPointExact

/-- Corrected K1.3 acceptance plus the projection bridge identifies the
production authenticated vector with final256 evaluations. -/
theorem ExactPreQ16OperationalK15Material.authenticatedQueryValuesExact
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {k13 : ExactPreQ16K13StageCertificate decoder input}
    {k14 : ExactPreQ16K14StageCertificate decoder decoderBinding input k13}
    {basis : Basis (Fin 4) F QM31Exact} {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    (material : ExactPreQ16OperationalK15Material input k12 k13 k14 basis rc
      poseidon) :
    exactTag73K13AuthenticatedQueryVector decoder input k12 =
      fun ordinal => exactFinalEncoder material.data.execution.disclosedFinal256
        ((exactK13ParsedProof input).queries ordinal) := by
  have correctedToExact := k13.authenticatedQueryVector_eq_exact k12
    material.source.sourceBinding material.source.openingPositions
  have disclosedExact : (exactK13ParsedProof input).disclosedFinal =
      material.data.execution.disclosedFinal256 := by
    calc
      (exactK13ParsedProof input).disclosedFinal =
          decodedFinalMessage material.data.decoded :=
        material.source.sourceBinding.disclosedFinalExact
      _ = (operationalFixedFields material.data.decoded).finalCoefficient := rfl
      _ = material.data.execution.disclosedFinal256 :=
        material.source.finalSource.disclosedFinalExact.symm
  calc
    exactTag73K13AuthenticatedQueryVector decoder input k12 =
        parsedK13AuthenticatedQueryVector k13.words
          (exactK13ParsedProof input) := correctedToExact.symm
    _ = fun ordinal => decoder.finalEncoder
          (exactK13ParsedProof input).disclosedFinal
          ((exactK13ParsedProof input).queries ordinal) := by
      funext ordinal
      simpa [parsedK13AuthenticatedQueryVector, parsedK13Transcript,
        decoderCodeEncoders, QueryConsistent, extractedIdealTranscript] using
        k13.parsed.accepts ordinal
    _ = fun ordinal => exactFinalEncoder
          material.data.execution.disclosedFinal256
          ((exactK13ParsedProof input).queries ordinal) := by
      rw [material.source.finalEncoderEq, disclosedExact]

#print axioms ExactPreQ16OperationalK15SourceBinding
#print axioms ExactPreQ16OperationalK15Material.authenticatedQueryValuesExact

end

end AspisK1.V7Tag73PreQ16OperationalK15Stage
