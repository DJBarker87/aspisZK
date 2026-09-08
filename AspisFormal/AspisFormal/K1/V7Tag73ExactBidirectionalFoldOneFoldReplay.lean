import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldProjection

/-!
# Exact scheduler replay from bidirectional fold/alpha coordinates

The five-coordinate equivalence is now used in both directions.  Holding its
residual and fold-work answer fixed while replacing the four alpha output
blocks gives one literal `runExactPlainRom` counterfactual.  At the actual raw
alpha coordinate, inverse cancellation reconstructs the original compiler
master tape exactly.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldProjection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

def exactAcceptedFoldBidirectionalRouter
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
    (fold : ExactAcceptedFoldTrial input) :
    ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters :=
  exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
    (exactAcceptedFoldPairTrial input fold).val
    (exactPlainRomCursor configuration sample.1).erase

def exactAcceptedFoldBidirectionalCoordinates
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
    (fold : ExactAcceptedFoldTrial input) :
    ExactCompilerBidirectionalFoldOneFoldResidual parameters ×
      (Digest256 × FourGammaBlocks) :=
  exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
    (exactAcceptedFoldBidirectionalRouter input fold) sample.2

/-- Put one residual and five named answers back into the exact master-tape
layout consumed by the production scheduler. -/
def exactBidirectionalFoldOneFoldTape
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters)
    (residual : ExactCompilerBidirectionalFoldOneFoldResidual parameters)
    (named : Digest256 × FourGammaBlocks) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length :=
  (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router).symm
    (residual, named)

@[simp] theorem exactBidirectionalFoldOneFoldTape_coordinates
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters)
    (residual : ExactCompilerBidirectionalFoldOneFoldResidual parameters)
    (named : Digest256 × FourGammaBlocks) :
    exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        (exactBidirectionalFoldOneFoldTape parameters router residual named) =
      (residual, named) := by
  exact Equiv.apply_symm_apply _ _

/-- Reassembling the actual coordinate tuple is literally the original tape. -/
theorem exactBidirectionalFoldOneFoldTape_of_actual
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    exactBidirectionalFoldOneFoldTape parameters router
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          tape).1
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          tape).2 = tape := by
  exact Equiv.symm_apply_apply _ _

/-- Literal result-carrying scheduler family obtained by replacing only the
four raw alpha output blocks.  Duplex-advance answers remain fixed in the
residual coordinate. -/
def exactBidirectionalFoldOneFoldRawReplay
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (hidden : HiddenTape)
    (router : ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters)
    (residual : ExactCompilerBidirectionalFoldOneFoldResidual parameters)
    (foldAnswer : Digest256) (raw : SuccessfulTag73RawStream) :
    SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) :=
  runExactPlainRom transitionFuel configuration
    (hidden, exactBidirectionalFoldOneFoldTape parameters router residual
      (foldAnswer, fourGammaBlocksRawEquiv.symm raw.1))

def exactAcceptedFoldCoordinateRaw
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) : SuccessfulTag73RawStream :=
  ⟨fourGammaBlocksRawEquiv
      (exactAcceptedFoldBidirectionalCoordinates input fold).2.2,
    exact_accepted_fold_probability_coordinate_alpha_succeeds
      transitionRoom programmedCover input fold⟩

theorem exactAcceptedFoldCoordinateRaw_value
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    successfulOrdinaryExactValue
        (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input
          fold) =
      exactOperationalChallenge input (.alpha 0) := by
  exact exact_accepted_fold_probability_coordinate_alpha_value
    transitionRoom programmedCover input fold

/-- The counterfactual family at the actual successful raw coordinate is
definitionally the original exact scheduler run. -/
theorem exactBidirectionalFoldOneFoldRawReplay_actual
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    exactBidirectionalFoldOneFoldRawReplay transitionFuel configuration sample.1
        (exactAcceptedFoldBidirectionalRouter input fold)
        (exactAcceptedFoldBidirectionalCoordinates input fold).1
        (exactAcceptedFoldBidirectionalCoordinates input fold).2.1
        (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input
          fold) =
      runExactPlainRom transitionFuel configuration sample := by
  unfold exactBidirectionalFoldOneFoldRawReplay
    exactAcceptedFoldCoordinateRaw exactAcceptedFoldBidirectionalCoordinates
  rw [fourGammaBlocksRawEquiv.symm_apply_apply]
  rw [exactBidirectionalFoldOneFoldTape_of_actual]

/-- The proof-relevant operational package exposes the literal completed
terminal of the original result-carrying scheduler run. -/
theorem exactOperationalPlainRom_terminal
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (runExactPlainRom transitionFuel configuration sample).terminal =
      .returned (.completed (exactK12Runtime input)
        input.package.root.full.clientRun) := by
  unfold runExactPlainRom
  rw [run_scheduler_native_eq_list_run]
  unfold runSchedulerNativeListRun
  rw [input.package.factorization.fullRunExact]
  dsimp only
  rw [input.package.factorization.computedClientTerminalExact]
  rfl

/-- Therefore the actual member of the counterfactual raw replay family
returns exactly the same production runtime and concrete client result. -/
theorem exactBidirectionalFoldOneFoldRawReplay_actual_terminal
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    (exactBidirectionalFoldOneFoldRawReplay transitionFuel configuration sample.1
        (exactAcceptedFoldBidirectionalRouter input fold)
        (exactAcceptedFoldBidirectionalCoordinates input fold).1
        (exactAcceptedFoldBidirectionalCoordinates input fold).2.1
        (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input
          fold)).terminal =
      .returned (.completed (exactK12Runtime input)
        input.package.root.full.clientRun) := by
  rw [exactBidirectionalFoldOneFoldRawReplay_actual transitionRoom
    programmedCover input fold]
  exact exactOperationalPlainRom_terminal input

#print axioms exactBidirectionalFoldOneFoldTape_coordinates
#print axioms exactBidirectionalFoldOneFoldTape_of_actual
#print axioms exactAcceptedFoldCoordinateRaw_value
#print axioms exactBidirectionalFoldOneFoldRawReplay_actual
#print axioms exactOperationalPlainRom_terminal
#print axioms exactBidirectionalFoldOneFoldRawReplay_actual_terminal

end
end AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
