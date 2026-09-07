import AspisFormal.K1.V7Tag73PreQ16OperationalK15Semantic

/-!
# Corrected pre-q16 operational K1.5 classifier

This final layer maps the semantic K1.5 disjunction to the literal
restoration-client extraction certificate or its typed residual event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16OperationalK15Classifier

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
open AspisK1.V7Tag73PreQ16OperationalK15Semantic
open AspisK1.V7Tag73PreQ16OperationalK15Stage
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Source/restoration provider for the corrected K1.5 material. -/
structure ExactPreQ16OperationalK15Environment
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
      deployedNullifier deployedNode) : Type where
  material : ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input)
      (k13 : ExactPreQ16K13StageCertificate decoder input)
      (k14 : ExactPreQ16K14StageCertificate decoder decoderBinding input k13),
    ExactPreQ16OperationalK15Material input k12 k13 k14 basis rc poseidon

/-- The proposition-level K1.5 decision. -/
theorem preQ16OperationalK15ResultNonempty
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
    (sample : ExactCompilerSample HiddenTape parameters)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k13 : ExactPreQ16K13StageCertificate decoder input)
    (k14 : ExactPreQ16K14StageCertificate decoder decoderBinding input k13)
    (material : ExactPreQ16OperationalK15Material input k12 k13 k14 basis rc
      poseidon) :
    Nonempty (ExactFixedClientExtractionCertificate transitionFuel configuration
        fixedInstance
        (exactTag73SpendRelation (deployedOwner := deployedOwner)
          (deployedNote := deployedNote)
          (deployedNullifier := deployedNullifier)
          (deployedNode := deployedNode)) sample ⊕
      ExactPreQ16OperationalK15Failure material) := by
  rcases AspisK1.V7Tag73PreQ16OperationalK15Semantic.ExactPreQ16OperationalK15Material.semanticClassifies
      material with
    valid | failure
  · exact ⟨.inl
      (exactFixedClientExtractionCertificateOfOperationalInput input
        material.clientExtractor
        (decodeTag73SpendWitness fixedInstance.statement
          k14.parsed.extraction)
        material.clientReturned material.clientExtracts valid)⟩
  · exact ⟨.inr ⟨failure⟩⟩

/-- Complete corrected operational K1.5 classifier. -/
noncomputable def classifyPreQ16OperationalK15
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
    (environment : ExactPreQ16OperationalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
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
      ExactPreQ16OperationalK15Failure
        (environment.material sample input k12 k13 k14) :=
  Classical.choice (preQ16OperationalK15ResultNonempty transitionFuel
    configuration projection fixedInstance decoder decoderBinding basis rc
    poseidon sample input k12 k13 k14
    (environment.material sample input k12 k13 k14))

#print axioms ExactPreQ16OperationalK15Failure
#print axioms preQ16OperationalK15ResultNonempty
#print axioms classifyPreQ16OperationalK15

end


end AspisK1.V7Tag73PreQ16OperationalK15Classifier
