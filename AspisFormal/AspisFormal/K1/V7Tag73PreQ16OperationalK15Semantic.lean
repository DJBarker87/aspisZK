import AspisFormal.K1.V7Tag73PreQ16OperationalK15Stage

/-!
# Corrected pre-q16 operational K1.5 semantics

This module isolates the normalization-heavy source theorem from both the
corrected extraction material and the restoration-client classifier.  The
split keeps each kernel term small enough for focused replay.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16OperationalK15Semantic

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73BatchedQuerySourceBridge
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73OperationalK15Classifier
open AspisK1.V7Tag73OperationalRelationSourceFacts
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73PreQ16OperationalK15Stage
open AspisK1.V7Tag73PreQ16OperationalRelationSourceFacts
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSpendK15FailureLedger
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeterministicSpendWitness
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- Run the normalization-heavy source theorem once, before constructing the
client extraction certificate. -/
theorem ExactPreQ16OperationalK15Material.semanticClassifies
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
    exactTag73SpendRelation (deployedOwner := deployedOwner)
        (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
        (deployedNode := deployedNode) fixedInstance
        (decodeTag73SpendWitness fixedInstance.statement
          k14.parsed.extraction) ∨
      CausalFailureEvidence
        (failureEvent basis rc fixedInstance.statement
          (operationalFixedFields material.data.decoded)
          (operationalAcceptedRun input material.data.decoded
            material.data.fixedDecode)
          (operationalCompactEvidence input material.data.decoded
            material.data.fixedDecode)
          k14.parsed.extraction
          (exactOperationalChallenge input .lambda)
          (exactOperationalChallenge input .chi)
          (exactOperationalChallenge input .theta)
          (fun coordinate => exactOperationalChallenge input
            (.zerocheckPoint coordinate))
          (exactOperationalChallenge input .mu) material.data.helper
          material.data.mask material.exactHonest
          (exactOperationalChallenge input .kappa) material.data.execution) := by
  unfold exactTag73SpendRelation
  have classified :=
    operational_parsed_k14_source_implies_decoded_witness_or_k15_failure input
      k14.parsed material.data.decoded material.data.fixedDecode
      material.source.sourceBinding basis rc poseidon fixedInstance.statement
      material.data.masks material.data.helper material.data.mask
      material.exactHonest material.source.maskInitialExact
      material.source.terminalOpeningExact material.source.inactiveSumZero
      material.data.execution material.source.initialEncoderEq
      material.source.executionInitialWeights
      material.source.executionInitialClaim material.source.inactiveExact
      material.source.finalSource
      (exactTag73K13AuthenticatedQueryVector decoder input k12)
      material.source.querySource.toOperationalSourceBinding
      material.authenticatedQueryValuesExact material.data.terminalSource
  exact classified.2

/-- Typed K1.5 residual for the corrected extraction. -/
structure ExactPreQ16OperationalK15Failure
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
      poseidon) : Type where
  evidence : CausalFailureEvidence
    (failureEvent basis rc fixedInstance.statement
      (operationalFixedFields material.data.decoded)
      (operationalAcceptedRun input material.data.decoded
        material.data.fixedDecode)
      (operationalCompactEvidence input material.data.decoded
        material.data.fixedDecode)
      k14.parsed.extraction
      (exactOperationalChallenge input .lambda)
      (exactOperationalChallenge input .chi)
      (exactOperationalChallenge input .theta)
      (fun coordinate => exactOperationalChallenge input
        (.zerocheckPoint coordinate))
      (exactOperationalChallenge input .mu) material.data.helper
      material.data.mask material.exactHonest
      (exactOperationalChallenge input .kappa) material.data.execution)

#print axioms ExactPreQ16OperationalK15Material.semanticClassifies
#print axioms ExactPreQ16OperationalK15Failure

end

end AspisK1.V7Tag73PreQ16OperationalK15Semantic
