import AspisFormal.K1.V7Tag73ExactRestoredOperationalStages
import AspisFormal.K1.V7Tag73ExactFixedOperationalNodeExecution
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
open AspisK1.V7Tag73ExactFixedOperationalNodeExecution
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ActualNodeCausalProvenance
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73RootGammaForkBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisK1.V7Tag73OperationalNodeCertificate
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

/-- Every literal accepted operational root supplies such a request.  This is
derived from the checked future-free transition list, not chosen from an
untyped SHA input. -/
theorem exact_operational_input_has_root_gamma_restoration_request
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    Nonempty (Σ request : ConcreteRestorationRequest,
      ExactRootGammaRestorationRequest input request) := by
  obtain ⟨transitionIndex, transition, reply, transitionExact, _within,
      eventExact⟩ :=
    exact_clean_root_has_indexed_gamma_transition
      input.package.root.fixedRoot.base
  exact ⟨⟨
    { nodeId := 0, verifierTransitionIndex := transitionIndex },
    { rootNode := rfl
      transition := transition
      reply := reply
      transitionExact := transitionExact
      eventExact := eventExact }
  ⟩⟩

/-- Canonical typed request used by downstream K1.4 source construction. -/
noncomputable def exactOperationalRootGammaRestorationRequest
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : ConcreteRestorationRequest :=
  (Classical.choice
    (exact_operational_input_has_root_gamma_restoration_request input)).1

/-- The canonical request retains its typed root-gamma provenance. -/
noncomputable def exact_operational_root_gamma_restoration_request_is_typed
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ExactRootGammaRestorationRequest input
      (exactOperationalRootGammaRestorationRequest input) :=
  (Classical.choice
    (exact_operational_input_has_root_gamma_restoration_request input)).2

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

/-- The scoped certificate names a node inserted by the executable dispatcher
for exactly its retained gamma request.  This exposes the scheduled fork coins
and both replay segments without trusting a source-supplied node map. -/
theorem gamma_restored_certificate_has_exact_projected_execution
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
    (positive : 0 < transitionFuel)
    (k13 : ExactGammaRestoredOperationalK13Certificate decoder input) :
    Nonempty { execution : ProjectedRestorationNodeExecution
        (Final := ConcreteRestorationClientRun Statement Tag73K12ParsedProof
          Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness))
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment configuration.restorationConfiguration
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactRestorationAccumulator input) k13.certificate.node //
      execution.prepared.request = k13.request } := by
  have nonroot : k13.certificate.node.parentRequest ≠ none := by
    rw [k13.parentRequestExact]
    exact Option.some_ne_none k13.request
  obtain ⟨execution⟩ := exact_operational_nonroot_node_has_projected_execution
    positive input k13.certificate.node k13.certificate.member nonroot
  have requestExact : execution.prepared.request = k13.request := by
    apply Option.some.inj
    exact execution.parentRequestExact.symm.trans k13.parentRequestExact
  exact ⟨⟨execution, requestExact⟩⟩

/-- The projected child execution selects the same literal root transition as
the typed request; the equality follows from executable preparation and the
immutable node-zero lookup. -/
theorem gamma_restored_certificate_execution_has_exact_transition
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
    (positive : 0 < transitionFuel)
    (k13 : ExactGammaRestoredOperationalK13Certificate decoder input) :
    Nonempty { execution : ProjectedRestorationNodeExecution
        (Final := ConcreteRestorationClientRun Statement Tag73K12ParsedProof
          Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness))
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment configuration.restorationConfiguration
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactRestorationAccumulator input) k13.certificate.node //
      execution.prepared.request = k13.request ∧
        execution.prepared.transition = k13.requestIsGamma.transition } := by
  obtain ⟨⟨execution, requestExact⟩⟩ :=
    gamma_restored_certificate_has_exact_projected_execution positive k13
  have selected := ready_preparation_parent_is_stored
    (configuration.machine.blackBox.start sample.1
      configuration.machine.observation)
    configuration.restorationConfiguration (exactRestorationAccumulator input)
    execution.prepared.request execution.prepared execution.preparationExact
  have rootLookup := input.package.root.full.projection.nodeStoreInvariant.1
  change (exactRestorationAccumulator input).node? 0 =
    some input.package.root.fixedRoot.base.runtime.node at rootLookup
  have parentExact : execution.prepared.parentNode =
      input.package.root.fixedRoot.base.runtime.node := by
    apply Option.some.inj
    calc
      some execution.prepared.parentNode =
          (exactRestorationAccumulator input).node?
            execution.prepared.request.nodeId := selected.1.symm
      _ = (exactRestorationAccumulator input).node? k13.request.nodeId := by
        rw [requestExact]
      _ = (exactRestorationAccumulator input).node? 0 := by
        rw [k13.requestIsGamma.rootNode]
      _ = some input.package.root.fixedRoot.base.runtime.node := rootLookup
  have selectedTransition := selected.2.2.2
  rw [requestExact, parentExact] at selectedTransition
  have transitionExact : execution.prepared.transition =
      k13.requestIsGamma.transition := by
    apply Option.some.inj
    exact selectedTransition.symm.trans k13.requestIsGamma.transitionExact
  exact ⟨⟨execution, requestExact, transitionExact⟩⟩

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
#print axioms exact_operational_input_has_root_gamma_restoration_request
#print axioms exactOperationalRootGammaRestorationRequest
#print axioms exact_operational_root_gamma_restoration_request_is_typed
#print axioms ExactGammaRestoredOperationalK13Certificate
#print axioms exactTag73GammaRestoredOperationalK14Width29Event
#print axioms gamma_restored_certificate_is_not_root
#print axioms gamma_restored_certificate_has_exact_projected_execution
#print axioms gamma_restored_certificate_execution_has_exact_transition
#print axioms gamma_restored_k14_width29_subset_unscoped

end
end AspisK1.V7Tag73GammaRestoredK14Scope
