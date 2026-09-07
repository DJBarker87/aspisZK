import AspisFormal.K1.V7Tag73K13PreQ16JointEventHandoff
import AspisFormal.K1.V7Tag73OperationalRelationSourceFacts

/-!
# Operational relation source facts for the corrected pre-q16 word

The original operational K1.5 source bridge was indexed by
`ExactK14Certificate`, whose extracted word is the completed prover history.
The corrected K1.3/K1.4 stages instead retain the word fixed immediately
before the selected final-work/q16 coordinate.  This module factors the
final-vector argument through the underlying parser-data coherent extraction.

No cryptographic check is removed: the execution must still expose its exact
initial values, disclosed final vector, and alpha-zero challenge, while the
literal production parser binds the disclosed vector to the decoded source.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16OperationalRelationSourceFacts

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73OperationalRelationSourceFacts
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73SemanticTranscriptBridge
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedDeployedCopyLaneCapstone
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CompactSemanticBinding
open AspisPool.V7DeterministicSpendWitness
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7InactiveClaimBinding
open AspisPool.V7PoseidonRowsFromTrace
open AspisPool.V7RelationCandidateBinding
open AspisPool.V7Tag73InactiveHelperAggregate
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriRelationCandidateBridge
open AspisV5SumcheckTranscriptBinding
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6QueryBatchSoundness
open AspisV6TranscriptRelationGrammar

noncomputable section

/-- Exact execution fields needed to identify the relation evaluator's final
vector with a parser-data coherent extraction.  This is the corrected-word
counterpart of `ExactFinal256ExecutionBinding`. -/
structure ExactParsedFinal256ExecutionBinding
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (extraction : CoherentTraceExtraction decoder binding words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule)
    (decoded : Fin 641 → QM31Exact)
    (execution : CandidateExecution QM31Exact) : Prop where
  initialValuesExact : execution.initialValues = extraction.combined.1
  disclosedFinalExact : execution.disclosedFinal256 =
    (operationalFixedFields decoded).finalCoefficient
  alphaZeroExact : execution.alpha 0 =
    (exactK13ParsedProof input).schedule.alpha

/-- Parser/source equality plus coherent folding proves the same positive
`Final256Matches` fact as the old exact-certificate bridge, now for the
corrected pre-q16 extraction. -/
theorem final256_matches_of_parsed_source_bindings
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {extraction : CoherentTraceExtraction decoder binding words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule}
    {decoded : Fin 641 → QM31Exact}
    {execution : CandidateExecution QM31Exact}
    (parsed : ExactParsedProofSourceBinding input decoded)
    (source : ExactParsedFinal256ExecutionBinding input words extraction decoded
      execution) :
    execution.Final256Matches := by
  unfold CandidateExecution.Final256Matches CandidateExecution.foldedInitial256
  calc
    execution.disclosedFinal256 =
        (operationalFixedFields decoded).finalCoefficient :=
      source.disclosedFinalExact
    _ = (exactK13ParsedProof input).disclosedFinal :=
      parsed.disclosedFinalExact.symm
    _ = coefficientFoldLayer 256
        (exactK13ParsedProof input).schedule.alpha extraction.combined.1 := by
      simpa [foldInitial] using extraction.foldsToDisclosedFinal.symm
    _ = coefficientFoldLayer 256 (execution.alpha 0)
        execution.initialValues := by
      rw [source.alphaZeroExact, source.initialValuesExact]

/-- The established old source record embeds definitionally into the generic
parser-data record.  This compatibility theorem checks that the factorization
does not alter the already verified completed-word path. -/
theorem parsedFinal256BindingOfExact
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : AspisK1.V7Tag73ExactFixedK12PrefixClassifier.ExactPrefixK12Certificate
      input}
    {k14 : AspisK1.V7Tag73ExactFixedK13K14Classifier.ExactK14Certificate
      decoder binding input k12}
    {decoded : Fin 641 → QM31Exact}
    {execution : CandidateExecution QM31Exact}
    (source : ExactFinal256ExecutionBinding k14 decoded execution) :
    ExactParsedFinal256ExecutionBinding input k12.words k14.extraction decoded
      execution where
  initialValuesExact := source.initialValuesExact
  disclosedFinalExact := source.disclosedFinalExact
  alphaZeroExact := source.alphaZeroExact

/-- The complete positive relation premise follows from the corrected
final-vector binding and the unchanged literal query/terminal source facts.
-/
theorem positive_relation_facts_of_parsed_source_bindings
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {extraction : CoherentTraceExtraction decoder binding words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule}
    {decoded : Fin 641 → QM31Exact}
    {execution : CandidateExecution QM31Exact}
    (parsed : ExactParsedProofSourceBinding input decoded)
    (finalSource : ExactParsedFinal256ExecutionBinding input words extraction
      decoded execution)
    (authenticated : QueryVector QM31Exact)
    (querySource : ExactQueryInjectionSourceBinding execution
      (exactK13ParsedProof input).queries
      (exactOperationalChallenge input .queryBatch) authenticated)
    (authenticatedExact : authenticated = fun ordinal =>
      exactFinalEncoder execution.disclosedFinal256
        ((exactK13ParsedProof input).queries ordinal))
    (terminalSource : ExactRelationTerminalSourceTrace execution) :
    execution.Final256Matches ∧ execution.QueryInjectionExact ∧
      execution.RelationTerminalAccepts := by
  exact ⟨final256_matches_of_parsed_source_bindings parsed finalSource,
    query_injection_exact_of_source_binding querySource authenticatedExact,
    relation_terminal_accepts_of_source_trace terminalSource⟩

set_option maxHeartbeats 5000000 in
/-- Source-facing operational K1.5 theorem for a parser-data K1.4
certificate.  It is the corrected-word counterpart of
`operational_k14_source_implies_decoded_witness_or_k15_failure`; every
semantic, transcript and source equality is unchanged except for the word
index carried by the coherent extraction. -/
theorem operational_parsed_k14_source_implies_decoded_witness_or_k15_failure
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
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
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (k14 : ParsedK14Certificate decoder decoderBinding words
      (exactK13ParsedProof input))
    (decoded : Fin 641 → QM31Exact)
    (fixedDecode : FixedFieldDecodeExact
      (rawOfMessages (exactOperationalTape input).messages) decoded)
    (sourceBinding : ExactParsedProofSourceBinding input decoded)
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (statement : V5PublicStatement)
    (masks : InactiveMasks)
    (helper mask : Fin 1024 → QM31Exact)
    (honest : FixedOracleTenRoundTrace
      (maskedOracle (operationalAcceptedRun input decoded fixedDecode).eta
        (extractedUnmaskedSemanticTable basis statement k14.extraction
          (deployedPoseidonRows rc (extractedPhysicalTrace k14.extraction))
          (deployedCompiledCopyLane
            (concreteDeployedCopyRegistryProjection k14.extraction)
            (exactOperationalChallenge input .lambda)
            (exactOperationalChallenge input .chi) helper)
          (exactOperationalChallenge input .theta)
          (fun coordinate => exactOperationalChallenge input
            (.zerocheckPoint coordinate))
          (exactOperationalChallenge input .mu) helper)
        mask)
      (operationalAcceptedRun input decoded fixedDecode).point)
    (maskInitialExact : (operationalFixedFields decoded).initialClaim =
      tableSum mask)
    (terminalOpeningExact :
      semanticTerminalClaim (operationalFixedFields decoded)
          (operationalAcceptedRun input decoded fixedDecode).point =
        claimAtStep
          (tableSum
            (maskedOracle (operationalAcceptedRun input decoded fixedDecode).eta
              (extractedUnmaskedSemanticTable basis statement k14.extraction
                (deployedPoseidonRows rc
                  (extractedPhysicalTrace k14.extraction))
                (deployedCompiledCopyLane
                  (concreteDeployedCopyRegistryProjection k14.extraction)
                  (exactOperationalChallenge input .lambda)
                  (exactOperationalChallenge input .chi) helper)
                (exactOperationalChallenge input .theta)
                (fun coordinate => exactOperationalChallenge input
                  (.zerocheckPoint coordinate))
                (exactOperationalChallenge input .mu) helper)
              mask))
          honest.messages
          (operationalAcceptedRun input decoded fixedDecode).point
          (Fin.last 10))
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
    (execution : CandidateExecution QM31Exact)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder)
    (executionInitialWeights : execution.initialWeights =
      extractedInitialRelationWeights masks
        (operationalAcceptedRun input decoded fixedDecode).point
        (exactOperationalChallenge input .kappa))
    (executionInitialClaim : execution.initialClaim =
      relationClaimBeforeOod (operationalFixedFields decoded)
        (exactK13ParsedProof input).gamma
        (exactOperationalChallenge input .kappa))
    (inactiveExact : (operationalFixedFields decoded).inactiveClaim =
      inactiveClaim masks k14.extraction.combined.1)
    (finalSource : ExactParsedFinal256ExecutionBinding input words
      k14.extraction decoded execution)
    (authenticated : QueryVector QM31Exact)
    (querySource : ExactQueryInjectionSourceBinding execution
      (exactK13ParsedProof input).queries
      (exactOperationalChallenge input .queryBatch) authenticated)
    (authenticatedExact : authenticated = fun ordinal =>
      exactFinalEncoder execution.disclosedFinal256
        ((exactK13ParsedProof input).queries ordinal))
    (terminalSource : ExactRelationTerminalSourceTrace execution) :
    ExactParsedProofSourceBinding input decoded ∧
      (let witness := decodeTag73SpendWitness statement k14.extraction
       (OpenedColumnsMatchStatement statement witness.opened ∧
        SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
          witness.opened witness.inputValue witness.outputValue) ∨
        CausalFailureEvidence
          (failureEvent basis rc statement (operationalFixedFields decoded)
            (operationalAcceptedRun input decoded fixedDecode)
            (operationalCompactEvidence input decoded fixedDecode)
            k14.extraction
            (exactOperationalChallenge input .lambda)
            (exactOperationalChallenge input .chi)
            (exactOperationalChallenge input .theta)
            (fun coordinate => exactOperationalChallenge input
              (.zerocheckPoint coordinate))
            (exactOperationalChallenge input .mu) helper mask honest
            (exactOperationalChallenge input .kappa) execution)) := by
  have positive := positive_relation_facts_of_parsed_source_bindings
    sourceBinding finalSource authenticated querySource authenticatedExact
      terminalSource
  refine ⟨sourceBinding, ?_⟩
  exact accepted_semantic_relation_implies_decoded_witness_or_causal_k15_failure
    basis rc poseidon statement masks (operationalFixedFields decoded)
    (operationalAcceptedRun input decoded fixedDecode)
    (operationalCompactEvidence input decoded fixedDecode) k14.extraction
    (exactOperationalChallenge input .lambda)
    (exactOperationalChallenge input .chi)
    (exactOperationalChallenge input .theta)
    (fun coordinate => exactOperationalChallenge input
      (.zerocheckPoint coordinate))
    (exactOperationalChallenge input .mu) helper mask honest maskInitialExact
    terminalOpeningExact inactiveSumZero
    (exactOperationalChallenge input .kappa) execution initialEncoderEq
    finalSource.initialValuesExact executionInitialWeights executionInitialClaim
    inactiveExact positive.1 positive.2.1 positive.2.2

#print axioms ExactParsedFinal256ExecutionBinding
#print axioms final256_matches_of_parsed_source_bindings
#print axioms parsedFinal256BindingOfExact
#print axioms positive_relation_facts_of_parsed_source_bindings
#print axioms operational_parsed_k14_source_implies_decoded_witness_or_k15_failure

end

end AspisK1.V7Tag73PreQ16OperationalRelationSourceFacts
