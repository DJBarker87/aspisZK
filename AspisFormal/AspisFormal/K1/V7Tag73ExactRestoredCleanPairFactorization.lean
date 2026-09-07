import AspisFormal.K1.V7Tag73ExactRestoredQ16ResidualFactorization
import AspisFormal.K1.V7Tag73K13CorrectedPairTrialProbability

/-!
# Sound restored Tag-73 K1.3 pair factorization

The older restored wrapper removed only final work and q16.  That factor is too
small after the explicit gamma/alpha-zero challenge bindings: equal residuals
do not by themselves fix the four alpha blocks or the earlier fold-work answer.

This module uses the exact 518-coordinate factor instead.  It conditions on the
corrected residual and four alpha blocks, indexes the accepted fold-work and
final-work trials separately, and leaves only the q16 forest random after both
work answers have been fixed.  No independence or grinding normalization is
assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactRestoredCleanPairFactorization

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AdaptiveFoldFinalWorkQ16TrialAccounting
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFoldArmedQ16Routing
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Events
open AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73K13CorrectedPairTrialProbability
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A restored K1.3 failure indexed by both literal work exposures. -/
structure ExactRestoredRootCleanK13PairTrialWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (sample : ExactCompilerSample HiddenTape parameters)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters) : Type where
  joint : ExactRestoredRootK13JointTrialWitness transitionFuel configuration
    projection fixedInstance decoder sample finalTrial
  legal : sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
    configuration projection fixedInstance
  foldExact : (exactAcceptedFoldTrial joint.input).trial = foldTrial

def exactRestoredRootCleanK13PairTrialEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | Nonempty (ExactRestoredRootCleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder sample foldTrial finalTrial)}

theorem exact_restored_clean_trial_union_subset_pair_trial_union
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact} :
    (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
        fixedInstance ∩
      ⋃ finalTrial : ExactCompilerExposureTrial parameters,
        exactRestoredRootK13JointTrialEvent transitionFuel configuration
          projection fixedInstance decoder finalTrial) ⊆
      ⋃ foldTrial : ExactCompilerExposureTrial parameters,
        ⋃ finalTrial : ExactCompilerExposureTrial parameters,
          exactRestoredRootCleanK13PairTrialEvent transitionFuel configuration
            projection fixedInstance decoder foldTrial finalTrial := by
  intro sample member
  rcases member with ⟨legal, member⟩
  obtain ⟨finalTrial, finalMember⟩ := Set.mem_iUnion.mp member
  let joint := Classical.choice finalMember
  let foldTrial := (exactAcceptedFoldTrial joint.input).trial
  apply Set.mem_iUnion.mpr
  refine ⟨foldTrial, Set.mem_iUnion.mpr ⟨finalTrial, ?_⟩⟩
  exact ⟨{ joint := joint, legal := legal, foldExact := rfl }⟩

/-- The bad set remains the source-derived restored set; adding a fold index
does not alter it. -/
noncomputable def exactRestoredRootCleanK13PairPointwiseBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) : Finset (Fin 262144) := by
  classical
  exact if member : Nonempty (ExactRestoredRootCleanK13PairTrialWitness
      transitionFuel configuration projection fixedInstance decoder sample
        foldTrial finalTrial) then
    (Classical.choice member).joint.bad
  else ∅

theorem exact_restored_clean_k13_pair_pointwise_bad_card
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (exactRestoredRootCleanK13PairPointwiseBad transitionFuel configuration
      projection fixedInstance decoder foldTrial finalTrial sample).card ≤ 9557 := by
  classical
  by_cases member : Nonempty (ExactRestoredRootCleanK13PairTrialWitness
      transitionFuel configuration projection fixedInstance decoder sample
        foldTrial finalTrial)
  · simpa [exactRestoredRootCleanK13PairPointwiseBad, member] using
      (Classical.choice member).joint.badCard
  · simp [exactRestoredRootCleanK13PairPointwiseBad, member]

/-- The exact source noninterference statement needed by the generic 518-slot
probability theorem.  Residual plus alpha, fold work, and final work are all
fixed; only q16 may vary. -/
def ExactRestoredRootCleanK13PairCoordinateInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length),
    (hidden, left) ∈ exactRestoredRootCleanK13PairTrialEvent transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial →
    (hidden, right) ∈ exactRestoredRootCleanK13PairTrialEvent transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial →
    let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1 →
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1 →
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1 →
    exactRestoredRootCleanK13PairPointwiseBad transitionFuel configuration
        projection fixedInstance decoder foldTrial finalTrial (hidden, left) =
      exactRestoredRootCleanK13PairPointwiseBad transitionFuel configuration
        projection fixedInstance decoder foldTrial finalTrial (hidden, right)

def exactRestoredRootCleanK13PairFibreNonempty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (context : ExactCompilerFoldAlphaFinalWorkQ16Residual parameters ×
      AlphaZeroDigestBlocks)
    (fold work : Digest256) : Prop :=
  let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
    transitionFuel foldTrial.val finalTrial.val
    (exactPlainRomCursor configuration hidden).erase
  ∃ tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length,
    (hidden, tape) ∈ exactRestoredRootCleanK13PairTrialEvent transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial ∧
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).1 = context ∧
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).2.1 = fold ∧
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
      tape).2.2.1 = work

noncomputable def exactRestoredRootCleanK13PairFibreBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (context : ExactCompilerFoldAlphaFinalWorkQ16Residual parameters ×
      AlphaZeroDigestBlocks)
    (fold work : Digest256) : Finset (Fin 262144) := by
  classical
  exact if inhabited : exactRestoredRootCleanK13PairFibreNonempty transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial hidden
        context fold work then
    exactRestoredRootCleanK13PairPointwiseBad transitionFuel configuration
      projection fixedInstance decoder foldTrial finalTrial
        (hidden, Classical.choose inhabited)
  else ∅

theorem exact_restored_clean_k13_pair_fibre_bad_card
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (context : ExactCompilerFoldAlphaFinalWorkQ16Residual parameters ×
      AlphaZeroDigestBlocks)
    (fold work : Digest256) :
    (exactRestoredRootCleanK13PairFibreBad transitionFuel configuration
      projection fixedInstance decoder foldTrial finalTrial hidden context fold
        work).card ≤ 9557 := by
  classical
  by_cases inhabited : exactRestoredRootCleanK13PairFibreNonempty transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial hidden
        context fold work
  · simpa [exactRestoredRootCleanK13PairFibreBad, inhabited] using
      exact_restored_clean_k13_pair_pointwise_bad_card
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) foldTrial
        finalTrial (hidden, Classical.choose inhabited)
  · simp [exactRestoredRootCleanK13PairFibreBad, inhabited]

theorem exact_restored_clean_k13_pair_fibre_bad_eq_pointwise
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (invariant : ExactRestoredRootCleanK13PairCoordinateInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (member : (hidden, tape) ∈
      exactRestoredRootCleanK13PairTrialEvent transitionFuel configuration
        projection fixedInstance decoder foldTrial finalTrial) :
    let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    exactRestoredRootCleanK13PairFibreBad transitionFuel configuration projection
        fixedInstance decoder foldTrial finalTrial hidden
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            tape).1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            tape).2.1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            tape).2.2.1 =
      exactRestoredRootCleanK13PairPointwiseBad transitionFuel configuration
        projection fixedInstance decoder foldTrial finalTrial (hidden, tape) := by
  classical
  let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
    transitionFuel foldTrial.val finalTrial.val
    (exactPlainRomCursor configuration hidden).erase
  let coordinates := exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates
    parameters router tape
  have inhabited : exactRestoredRootCleanK13PairFibreNonempty transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial hidden
        coordinates.1 coordinates.2.1 coordinates.2.2.1 :=
    ⟨tape, member, rfl, rfl, rfl⟩
  let representative := Classical.choose inhabited
  have facts := Classical.choose_spec inhabited
  have sameBad := invariant foldTrial finalTrial hidden representative tape
    facts.1 member facts.2.1 facts.2.2.1 facts.2.2.2
  simpa [exactRestoredRootCleanK13PairFibreBad, inhabited, router, coordinates,
    representative] using sameBad

noncomputable def exactRestoredRootCleanK13PairExposureTrials
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (invariant : ExactRestoredRootCleanK13PairCoordinateInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1)) :
    ExactCompilerExposurePairIndexedFoldAlphaFinalWorkQ16Trials
      (HiddenTape := HiddenTape) parameters where
  event := exactRestoredRootCleanK13PairTrialEvent transitionFuel configuration
    projection fixedInstance decoder
  router := fun foldTrial finalTrial hidden =>
    exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
      foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
  bad := fun foldTrial finalTrial hidden residual alpha fold work =>
    exactRestoredRootCleanK13PairFibreBad transitionFuel configuration projection
      fixedInstance decoder foldTrial finalTrial hidden (residual, alpha) fold work
  badCard := fun foldTrial finalTrial hidden residual alpha fold work =>
    exact_restored_clean_k13_pair_fibre_bad_card
      (configuration := configuration) (projection := projection)
      (fixedInstance := fixedInstance) (decoder := decoder) foldTrial finalTrial
      hidden (residual, alpha) fold work
  reference := reference
  traceExists := traceExists
  covered := by
    intro foldTrial finalTrial hidden tape member
    change Nonempty (ExactRestoredRootCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, tape) foldTrial
        finalTrial) at member
    let witness := Classical.choice member
    let realization := Classical.choice
      (exact_compiler_accepted_fold_armed_q16_operational_realization
        transitionRoom programmedCover witness.joint.input
          (frontierExact (hidden, tape) witness.joint.input))
    have finalExact : realization.anchor.source.finalTrial = finalTrial := by
      rw [realization.anchor.sourceExact]
      exact (witness.joint.trialExact transitionRoom).symm
    let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    have routerExact : realization.anchor.router = router := by
      rw [realization.anchor.routerExact, realization.anchor.foldExact,
        finalExact, witness.foldExact]
    let coordinates := exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates
      parameters router tape
    have q16Success : q16DigestForestSucceeds
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
          realization.anchor.router tape).2.2.2 :=
      operational_realization_implies_q16_digest_forest_succeeds
        realization.forestRealized
    have pointwiseExact :
        exactRestoredRootCleanK13PairPointwiseBad transitionFuel configuration
          projection fixedInstance decoder foldTrial finalTrial (hidden, tape) =
            witness.joint.bad := by
      simp [exactRestoredRootCleanK13PairPointwiseBad, member, witness]
    have fibreExact := exact_restored_clean_k13_pair_fibre_bad_eq_pointwise
      invariant foldTrial finalTrial hidden tape member
    have badExact : exactRestoredRootCleanK13PairFibreBad transitionFuel
        configuration projection fixedInstance decoder foldTrial finalTrial hidden
          coordinates.1 coordinates.2.1 coordinates.2.2.1 = witness.joint.bad := by
      simpa [router, coordinates] using fibreExact.trans pointwiseExact
    obtain ⟨_digest, _workAnswer, _base, _workAccepted, _prefinal,
      _baseExact, _pairLabeled, _workLabeled, _workCoordinate, oldRealized⟩ :=
        witness.joint.actualTrial
    rcases witness.joint.coordinate with ⟨_oldSuccess, oldBadMember⟩
    have oldSuccessQ16 : q16DigestForestSucceeds
        (exactRestoredRootK13TrialCoordinates transitionFuel configuration
          finalTrial (hidden, tape)).2.2 := _oldSuccess
    have oldQ16BadRestored : successfulQ16DigestForestEquiv
        ⟨(exactRestoredRootK13TrialCoordinates transitionFuel configuration
          finalTrial (hidden, tape)).2.2, oldSuccessQ16⟩ ∈
          q16SuccessfulCoordinatesBadEvent witness.joint.bad := by
      exact oldBadMember.2
    have oldRealizedSuccess : q16DigestForestSucceeds
        (exactFixedK13TrialCoordinates transitionFuel configuration finalTrial
          (hidden, tape)).2.2 :=
      operational_realization_implies_q16_digest_forest_succeeds oldRealized
    have oldQ16Bad : successfulQ16DigestForestEquiv
        ⟨(exactFixedK13TrialCoordinates transitionFuel configuration finalTrial
          (hidden, tape)).2.2, oldRealizedSuccess⟩ ∈
          q16SuccessfulCoordinatesBadEvent witness.joint.bad := by
      simpa [exactRestoredRootK13TrialCoordinates,
        exactFixedK13TrialCoordinates] using oldQ16BadRestored
    have allBad : AllInBad witness.joint.bad
        (semanticScheduleOfOperational
          (exactOperationalTape witness.joint.input).search.selectedSchedule) := by
      rw [q16SuccessfulCoordinatesBadEvent, Set.mem_setOf_eq,
        successful_forest_equiv_selected_exact oldRealized] at oldQ16Bad
      exact oldQ16Bad
    have q16Bad := operational_all_in_bad_implies_successful_coordinate_bad
      realization.forestRealized witness.joint.bad allBad
    have badExactAnchor : exactRestoredRootCleanK13PairFibreBad transitionFuel
        configuration projection fixedInstance decoder foldTrial finalTrial
        hidden
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).2.1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).2.2.1 = witness.joint.bad := by
      rw [routerExact]
      exact badExact
    simp only [Set.mem_preimage]
    change (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
      router tape) ∈ dependentSuccessfulSubtypeEvent _ _
    rw [← routerExact]
    refine ⟨q16Success, ?_⟩
    change FoldWork31Accepted _ ∧ FinalWork34Accepted _ ∧ _
    refine ⟨realization.anchor.foldCoordinate ▸
      realization.anchor.fold.accepted,
      realization.anchor.workCoordinate ▸
        realization.anchor.source.workAccepted, ?_⟩
    change successfulQ16DigestForestEquiv
        ⟨(exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
          realization.anchor.router tape).2.2.2, q16Success⟩ ∈
      q16SuccessfulCoordinatesBadEvent
        (exactRestoredRootCleanK13PairFibreBad transitionFuel configuration
          projection fixedInstance decoder foldTrial finalTrial hidden
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).2.1
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            realization.anchor.router tape).2.2.1)
    rw [badExactAnchor]
    exact q16Bad

theorem exact_restored_clean_pair_trial_union_probability_le_one_forest
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (invariant : ExactRestoredRootCleanK13PairCoordinateInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ foldTrial, ⋃ finalTrial,
          exactRestoredRootCleanK13PairTrialEvent transitionFuel configuration
            projection fixedInstance decoder foldTrial finalTrial) ≤
      q16SemanticOneForestRawError := by
  let trials := exactRestoredRootCleanK13PairExposureTrials transitionFuel
    configuration projection fixedInstance decoder transitionRoom programmedCover
      frontierExact invariant reference traceExists
  exact trials.failure_union_probability_le_one_forest foldExposureCap
    finalExposureCap

theorem exact_restored_clean_trial_union_probability_le_one_forest
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (invariant : ExactRestoredRootCleanK13PairCoordinateInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          ⋃ finalTrial : ExactCompilerExposureTrial parameters,
            exactRestoredRootK13JointTrialEvent transitionFuel configuration
              projection fixedInstance decoder finalTrial) ≤
      q16SemanticOneForestRawError := by
  calc
    _ ≤ (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ foldTrial, ⋃ finalTrial,
          exactRestoredRootCleanK13PairTrialEvent transitionFuel configuration
            projection fixedInstance decoder foldTrial finalTrial) := by
      apply measure_mono
      exact exact_restored_clean_trial_union_subset_pair_trial_union
    _ ≤ q16SemanticOneForestRawError :=
      exact_restored_clean_pair_trial_union_probability_le_one_forest hiddenLaw
        transitionRoom programmedCover frontierExact invariant reference
          traceExists foldExposureCap finalExposureCap

#print axioms ExactRestoredRootCleanK13PairTrialWitness
#print axioms exact_restored_clean_trial_union_subset_pair_trial_union
#print axioms exact_restored_clean_k13_pair_pointwise_bad_card
#print axioms ExactRestoredRootCleanK13PairCoordinateInvariant
#print axioms exact_restored_clean_k13_pair_fibre_bad_card
#print axioms exact_restored_clean_k13_pair_fibre_bad_eq_pointwise
#print axioms exactRestoredRootCleanK13PairExposureTrials
#print axioms exact_restored_clean_pair_trial_union_probability_le_one_forest
#print axioms exact_restored_clean_trial_union_probability_le_one_forest

end

end AspisK1.V7Tag73ExactRestoredCleanPairFactorization
