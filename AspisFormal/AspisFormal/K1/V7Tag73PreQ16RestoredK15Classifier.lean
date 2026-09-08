import AspisFormal.K1.V7Tag73PreQ16RestoredK15Context

/-!
# Restoration-aware classifier for corrected pre-q16 K1.5

The classifier first preserves direct operational extraction, then routes any
point-compatible restored branch to client extraction.  Its only residual data
is the exact fixed-family branch or a raw causal failure with both extraction
routes ruled out.  The separate event-cover theorem reduces that latter case to
the constrained gamma event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16RestoredK15Classifier

open Module
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73OperationalClientExtractionBridge
open AspisK1.V7Tag73PreQ16OperationalK15Classifier
open AspisK1.V7Tag73PreQ16OperationalK15Stage
open AspisK1.V7Tag73PreQ16RestoredK15Context
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Corrected restoration-aware K1.5 decision. -/
noncomputable def classifyPreQ16RestoredK15
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters)
    (projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload)
    (fixedInstance : PublicInstance V5PublicStatement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (basis : Basis (Fin 4) F QM31Exact) (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (environment : ExactPreQ16RestoredK15Environment transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon)
    (sample : ExactCompilerSample HiddenTape parameters)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k13 : ExactPreQ16K13StageCertificate decoder input)
    (k14 : ExactPreQ16K14StageCertificate decoder decoderBinding input k13) :
    ExactFixedClientExtractionCertificate transitionFuel configuration
        fixedInstance
        (exactTag73SpendRelation (deployedOwner := deployedOwner)
          (deployedNote := deployedNote)
          (deployedNullifier := deployedNullifier)
          (deployedNode := deployedNode)) sample ⊕
      ExactPreQ16RestoredK15Failure environment
        ⟨sample, input, k12, k13, k14⟩ := by
  let context : ExactPreQ16K15Context transitionFuel configuration projection
      fixedInstance decoder decoderBinding := ⟨sample, input, k12, k13, k14⟩
  match classifyPreQ16OperationalK15 transitionFuel configuration projection
      fixedInstance decoder decoderBinding basis rc poseidon
      environment.operational sample input k12 k13 k14 with
  | .inl extracted => exact .inl extracted
  | .inr failure =>
      by_cases anyFixed : context.fixedFailure environment
      · exact .inr ⟨Or.inl anyFixed⟩
      · by_cases restored : HasAcceptedRestoredPointCompatibleK14 decoder
            context.k13.words (context.run environment.operational).point
            (context.fields environment.operational).pointClaim
            (environment.family context)
        · let restoredResult := Classical.choice
            (environment.pointCompatibleResult context anyFixed restored)
          exact .inl
            (exactFixedClientExtractionCertificateOfOperationalInput
              context.input restoredResult.extractor restoredResult.witness
              restoredResult.clientReturned restoredResult.extractorReturned
              restoredResult.relationValid)
        · exact .inr ⟨Or.inr ⟨⟨failure⟩, anyFixed, restored⟩⟩

#print axioms classifyPreQ16RestoredK15

end

end AspisK1.V7Tag73PreQ16RestoredK15Classifier
