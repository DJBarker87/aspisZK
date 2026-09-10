import AspisFormal.K1.V7Tag73ExactRestoredOperationalStages
import AspisFormal.K1.V7Tag73RootGammaForkBridge

/-!
# Provenance scope for the restoration-native K1.4 challenge

The fresh gamma coordinate used by the K1.4 width bound belongs to a concrete
restoration request at the root's block-zero gamma transition.  A certificate
on the original root, or on a child restored at another transition, cannot be
silently measured under that coordinate.  These types make the required
request and node provenance explicit.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73GammaRestoredK14Scope

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- One concrete request selects block zero of the root verifier's gamma
squeeze before either programmed answer is exposed. -/
structure ExactRootGammaRestorationRequest
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
    (request : ConcreteRestorationRequest) : Type where
  rootNode : request.nodeId = 0
  transition : FutureFreeTransition
  reply : VerifierReply
  transitionExact : verifierTransitionAt?
      input.package.root.fixedRoot.base.runtime.node
      request.verifierTransitionIndex = some transition
  eventExact : transition.event =
    .verifier (.squeezePair (.challenge .gamma) 0) reply

/-- A restoration-wide K1.3 certificate whose node was actually created by
the selected root-gamma request.  `parentRequestExact` excludes the original
root and every unrelated restored child by construction. -/
structure ExactGammaRestoredOperationalK13Certificate
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
  request : ConcreteRestorationRequest
  requestIsGamma : ExactRootGammaRestorationRequest input request
  certificate : ExactRestoredOperationalK13Certificate decoder input
  parentRequestExact : certificate.node.parentRequest = some request

/-- The correctly scoped width-29 event for the fresh restoration-native
gamma law.  The old unscoped event also admitted the original root, whose
gamma answer is not the selected restored-fork coordinate. -/
def exactTag73GammaRestoredOperationalK14Width29Event
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k13 : ExactGammaRestoredOperationalK13Certificate decoder input),
    Width29DecompositionFailure decoder
      k13.certificate.classified.k12.words
      (restoredOperationalK13View k13.certificate.data).gamma
      (restoredOperationalK13View k13.certificate.data).disclosedFinal
      (restoredOperationalK13View k13.certificate.data).schedule}

/-- A gamma-restored certificate can never be the literal root node. -/
theorem gamma_restored_certificate_is_not_root
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
    (k13 : ExactGammaRestoredOperationalK13Certificate decoder input) :
    k13.certificate.node ≠ input.package.root.fixedRoot.base.runtime.node := by
  intro nodeExact
  have rootParent : input.package.root.fixedRoot.base.runtime.node.parentRequest =
      none := by
    rfl
  have childParent := k13.parentRequestExact
  rw [nodeExact, rootParent] at childParent
  cases childParent

/-- Forgetting provenance embeds the corrected event into the older broad
event.  The converse is deliberately absent. -/
theorem gamma_restored_k14_width29_subset_unscoped
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact} :
    exactTag73GammaRestoredOperationalK14Width29Event transitionFuel
        configuration projection fixedInstance decoder ⊆
      AspisK1.V7Tag73ExactRestoredOperationalStages.exactTag73RestoredOperationalK14Width29Event
        transitionFuel configuration projection fixedInstance decoder := by
  rintro sample ⟨input, k13, failure⟩
  exact ⟨input, k13.certificate, failure⟩

#print axioms ExactRootGammaRestorationRequest
#print axioms ExactGammaRestoredOperationalK13Certificate
#print axioms exactTag73GammaRestoredOperationalK14Width29Event
#print axioms gamma_restored_certificate_is_not_root
#print axioms gamma_restored_k14_width29_subset_unscoped

end
end AspisK1.V7Tag73GammaRestoredK14Scope
