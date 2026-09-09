import AspisFormal.K1.V7Tag73CanonicalOneFoldSchedule
import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events
import AspisFormal.K1.V7Tag73ExactRestoredQ16JointEventHandoff
import AspisFormal.K1.V7Tag73ExactRestoredQ16SemanticNoninterference
import AspisFormal.K1.V7Tag73K13PreQ16QueryHandoff

/-!
# Literal parsed view equals the verifier-derived restored root view

The restoration-wide K1.3 classifier deliberately reconstructs gamma,
alpha-zero and q16 from verifier state instead of trusting the parser-owned
fields.  On the literal accepted root, the production source bindings prove
that both descriptions nevertheless denote the same mathematical proof.

This bridge is data-level only.  It assumes canonical fixed-field decoding
and the existing parser/source equalities; it introduces no probability or
acceptance premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73RestoredRootParsedViewBridge

open AspisK1.V7FsAokExperiment
open AspisCircleGroupOrder
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73CurrentSourceDecodeBridge
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactRestoredQ16JointEventHandoff
open AspisK1.V7Tag73ExactRestoredQ16SemanticNoninterference
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73K13PreQ16QueryHandoff
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-! Keep the small schedule-uniqueness argument local.  Compiling the older
standalone uniqueness module causes Lean's optional library-suggestion
serializer to retain a disproportionate environment; the factored proof here
uses the same equations without that build-time memory cost. -/

private theorem inverse_entry_unique
    (multiplier : QM31Exact) (left right : M31Exact)
    (leftExact : multiplier * algebraMap M31Exact QM31Exact left = 1)
    (rightExact : multiplier * algebraMap M31Exact QM31Exact right = 1) :
    left = right := by
  apply FaithfulSMul.algebraMap_injective M31Exact QM31Exact
  have multiplierNonzero : multiplier ≠ 0 := by
    intro zero
    rw [zero] at leftExact
    norm_num at leftExact
  apply mul_left_cancel₀ multiplierNonzero
  exact leftExact.trans rightExact.symm

private theorem schedule_eq_canonical
    (schedule : ExactSchedule)
    (tables : ExactOneFoldInverseTables schedule) :
    schedule = canonicalOneFoldSchedule schedule.alpha := by
  cases schedule with
  | mk alpha inverseTwoX inverseTwoY =>
      dsimp only at tables ⊢
      have xExact : inverseTwoX =
          (canonicalOneFoldSchedule alpha).circleInv2x := by
        funext index
        exact inverse_entry_unique (2 * exactCircleX index)
          (inverseTwoX index)
          ((canonicalOneFoldSchedule alpha).circleInv2x index)
          (tables.1 index) ((canonical_one_fold_schedule_exact alpha).1 index)
      have yExact : inverseTwoY =
          (canonicalOneFoldSchedule alpha).circleInv2y := by
        funext index
        exact inverse_entry_unique (2 * exactCircleY index)
          (inverseTwoY index)
          ((canonicalOneFoldSchedule alpha).circleInv2y index)
          (tables.2 index) ((canonical_one_fold_schedule_exact alpha).2 index)
      cases xExact
      cases yExact
      rfl

/-- Canonical decoding forces the restored provider's 641 field elements to
equal the source bridge's decoded vector pointwise. -/
theorem exact_restored_root_decoded_eq_source
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (data : RestoredOperationalK13Data configuration.machine.environment
      input.package.root.fixedRoot.base.runtime.node)
    (decoded : Fin 641 → QM31Exact)
    (sourceDecode : CurrentSourceFixedFieldProjection
      input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages
      decoded) :
    data.decoded = decoded := by
  funext index
  have rightDecode :=
    current_source_fixed_field_projection_implies_decode sourceDecode index
  exact Option.some.inj ((data.fixedDecode index).symm.trans rightDecode)

/-- On the accepted root, the corrected verifier-derived K1.3 view is exactly
the parser view consumed by the relation source.  In particular, switching to
the restored classifier changes no mathematics and trusts no parser-owned
challenge or q16 schedule. -/
theorem exact_restored_root_k13_view_eq_parsed_of_source
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
    (decoded : Fin 641 → QM31Exact)
    (sourceDecode : CurrentSourceFixedFieldProjection
      input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages
      decoded)
    (binding : ExactParsedProofSourceBinding input decoded) :
    exactRestoredRootK13View input = exactK13ParsedProof input := by
  let node := input.package.root.fixedRoot.base.runtime.node
  let data :=
    (exact_restored_operational_k13_provider input).data node
      (exact_restoration_accumulator_contains_root input)
      (exact_restoration_accumulator_root_is_done input)
  have decodedExact : data.decoded = decoded :=
    exact_restored_root_decoded_eq_source input data decoded sourceDecode
  have challenges :=
    exact_restored_root_operational_data_challenges_are_source_exact input data
  have scheduleExact : (exactK13ParsedProof input).schedule =
      canonicalOneFoldSchedule
        (exactOperationalChallenge input (.alpha 0)) := by
    calc
      (exactK13ParsedProof input).schedule =
          canonicalOneFoldSchedule
            (exactK13ParsedProof input).schedule.alpha :=
        schedule_eq_canonical _ binding.inverseTablesExact
      _ = canonicalOneFoldSchedule
          (exactOperationalChallenge input (.alpha 0)) := by
        rw [binding.alphaZeroExact]
  have selectedExact :=
    exact_root_k13_data_selected_schedule_eq_operational input data
  have gammaExact : data.gamma = (exactK13ParsedProof input).gamma := by
    rw [challenges.2.1]
    exact binding.gammaExact.symm
  have finalExact : decodedFinalMessage data.decoded =
      (exactK13ParsedProof input).disclosedFinal := by
    rw [decodedExact]
    exact binding.disclosedFinalExact.symm
  have proofScheduleExact : canonicalOneFoldSchedule data.alphaZero =
      (exactK13ParsedProof input).schedule := by
    rw [challenges.2.2.2]
    exact scheduleExact.symm
  have queriesExact : data.selectedSchedule.positions =
      (exactK13ParsedProof input).queries := by
    rw [selectedExact]
    exact binding.selectedQueriesExact.symm
  have openingsExact :
      (restoredNodeK12Proof node).openings =
        (exactK13ParsedProof input).openings := by
    rfl
  change restoredOperationalK13View data = exactK13ParsedProof input
  cases proofExact : exactK13ParsedProof input with
  | mk openings gamma disclosedFinal schedule queries =>
      simp only [proofExact] at gammaExact finalExact proofScheduleExact queriesExact ⊢
      cases gammaExact
      cases finalExact
      cases proofScheduleExact
      cases queriesExact
      unfold restoredOperationalK13View
      rw [openingsExact]
      rw [proofExact]

/-- A restored-root ideal rejection is therefore a rejection for the exact
prefix K1.2 word as well.  The only non-definitional step is locality of one
circle-fold query: both words project the same authenticated paired opening.
This is the deterministic bridge needed to reuse the frozen degree-sixteen
joint-batch algebra on the restoration-wide event. -/
theorem restored_root_ideal_rejected_implies_prefix_ideal_rejected
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
    (restoredK12 : RestoredNodeK12Certificate
      input.package.root.fixedRoot.base.runtime.node)
    (prefixK12 : ExactPrefixK12Certificate input)
    (decoded : Fin 641 → QM31Exact)
    (sourceDecode : CurrentSourceFixedFieldProjection
      input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages
      decoded)
    (binding : ExactParsedProofSourceBinding input decoded)
    (positions : ExactOpeningPositionsSourceBinding input)
    (rejected : ¬ IdealAccepts (exactRestoredRootK13View input).schedule
      (exactK13Encoders decoder)
      (parsedK13Transcript restoredK12.words
        (exactRestoredRootK13View input))
      (exactRestoredRootK13View input).queries) :
    ¬ IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input prefixK12)
      (exactK13ParsedProof input).queries := by
  intro prefixAccepts
  apply rejected
  have viewExact := exact_restored_root_k13_view_eq_parsed_of_source input
    decoded sourceDecode binding
  rw [viewExact]
  intro ordinal
  let opening := exactK12Openings input ordinal
  have restoredProjection : openingIsProjection restoredK12.words opening := by
    exact restoredK12.rootsAndOpenings.2 ordinal
  have prefixProjection : openingIsProjection prefixK12.words opening :=
    prefixK12.projections ordinal
  have positionExact : ((exactK13ParsedProof input).queries ordinal).val =
      opening.position.val := by
    rw [binding.selectedQueriesExact]
    exact (positions ordinal).symm
  exact query_consistent_of_shared_projected_opening
    (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
    prefixK12.words restoredK12.words opening prefixProjection
    restoredProjection (exactK13ParsedProof input).gamma
    (exactK13ParsedProof input).disclosedFinal
    ((exactK13ParsedProof input).queries ordinal) positionExact
    (prefixAccepts ordinal)

/-- The frozen Tag-73 algebraic dichotomy now applies verbatim to the
restored-root rejection: either the query-batch challenge hits the explicit
degree-sixteen collision set, or a later relation alpha repairs a nonzero
discrepancy.  All conversion premises are source/data equalities. -/
theorem restored_root_ideal_rejected_exposes_joint_or_later_collision
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (restoredK12 : RestoredNodeK12Certificate
      input.package.root.fixedRoot.base.runtime.node)
    (prefixK12 : ExactPrefixK12Certificate input)
    (decoded : Fin 641 → QM31Exact)
    (sourceDecode : CurrentSourceFixedFieldProjection
      input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages
      decoded)
    (binding : ExactParsedProofSourceBinding input decoded)
    (positions : ExactOpeningPositionsSourceBinding input)
    (rejected : ¬ IdealAccepts (exactRestoredRootK13View input).schedule
      (exactK13Encoders decoder)
      (parsedK13Transcript restoredK12.words
        (exactRestoredRootK13View input))
      (exactRestoredRootK13View input).queries) :
    (exactTag73K13ExpectedQueryVector decoder input prefixK12 ≠
          exactTag73K13AuthenticatedQueryVector decoder input prefixK12 ∧
        exactOperationalChallenge input .queryBatch ∈
          jointQueryBatchNonzeroCollisionSet
            (source.preQueryDiscrepancy sample input)
            (exactTag73K13ExpectedQueryVector decoder input prefixK12)
            (exactTag73K13AuthenticatedQueryVector decoder input prefixK12)) ∨
      ∃ round : Fin 4, 0 < round.val ∧
        (source.execution sample input).discrepancyTrace.AlphaRepair round := by
  have prefixRejected :=
    restored_root_ideal_rejected_implies_prefix_ideal_rejected decoder input
      restoredK12 prefixK12 decoded sourceDecode binding positions rejected
  have different : exactTag73K13ExpectedQueryVector decoder input prefixK12 ≠
      exactTag73K13AuthenticatedQueryVector decoder input prefixK12 := by
    intro equal
    exact prefixRejected
      ((exactTag73K13IdealAccepts_iff_query_vectors_eq decoder input
        prefixK12).2 equal)
  have rhoNonzero : exactOperationalChallenge input .queryBatch ≠ 0 :=
    (exact_operational_input_constructs_post_eta_nonzero_challenges input).2.2
  exact joint_collision_or_later_alphaRepair
    (source.execution sample input)
    (source.preQueryDiscrepancy sample input)
    (exactTag73K13ExpectedQueryVector decoder input prefixK12)
    (exactTag73K13AuthenticatedQueryVector decoder input prefixK12)
    (exactOperationalChallenge input .queryBatch) rhoNonzero different
    (source.beforeOneExact sample input prefixK12)
    (source.relationTerminal sample input)

#print axioms exact_restored_root_decoded_eq_source
#print axioms exact_restored_root_k13_view_eq_parsed_of_source
#print axioms restored_root_ideal_rejected_implies_prefix_ideal_rejected
#print axioms restored_root_ideal_rejected_exposes_joint_or_later_collision

end
end AspisK1.V7Tag73RestoredRootParsedViewBridge
