import AspisFormal.K1.V7Tag73CounterfactualOneFoldReplayFilter
import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldReplay

/-!
# Actual accepted proof in the executable one-fold replay family

For one accepted seed execution, the exact source binding identifies the
deployed schedule alpha with the mathematical value returned by the routed raw
sampler.  Hence the executable filter contains the literal production proof at
the actual coordinate.  Counterfactual runs which fail or return incoherent
gamma/schedule data remain mapped to `none`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplayFilter

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73CounterfactualOneFoldProvider
open AspisK1.V7Tag73CounterfactualOneFoldReplayFilter
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactOneFoldRestorationStrategy
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The actual successful raw coordinate paired with a dummy advance ghost.
The literal replay ignores this ghost because the real deployed advance
answers remain inside the bidirectional residual. -/
def exactAcceptedFoldCoordinateAttempt
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
    SuccessfulTag73DuplexOrdinaryAttempt :=
  (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input fold,
    fun _ => fold.answer)

/-- Executable future-free parsed-proof family for one fixed residual/fold
slice. -/
def exactAcceptedFoldReplayOracle
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (words : ExtractedWords)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    CounterfactualParsedOneFoldOracle words (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).schedule :=
  counterfactualParsedOneFoldOracleOfPlainRomReplay
    (exactK13ParsedProof input).gamma (exactK13ParsedProof input).schedule
    (exactK13ParsedProof input).disclosedFinal
    (fun attempt => exactBidirectionalFoldOneFoldRawReplay transitionFuel
      configuration sample.1 (exactAcceptedFoldBidirectionalRouter input fold)
      (exactAcceptedFoldBidirectionalCoordinates input fold).1
      (exactAcceptedFoldBidirectionalCoordinates input fold).2.1 attempt.1)

/-- The actual accepted production proof is present in the executable replay
oracle.  The only source-facing input is the existing data-only parsed-proof
binding; no probability or extraction conclusion is assumed. -/
theorem exactAcceptedFoldReplayOracle_actualProof
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoded : Fin 641 → QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (words : ExtractedWords)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (source : ExactParsedProofSourceBinding input decoded) :
    (exactAcceptedFoldReplayOracle words input fold).proof?
        (exactAcceptedFoldCoordinateAttempt transitionRoom programmedCover input
          fold) =
      some (exactK13ParsedProof input) := by
  let actual := exactAcceptedFoldCoordinateAttempt transitionRoom
    programmedCover input fold
  let replay := fun attempt : SuccessfulTag73DuplexOrdinaryAttempt =>
    exactBidirectionalFoldOneFoldRawReplay transitionFuel configuration sample.1
      (exactAcceptedFoldBidirectionalRouter input fold)
      (exactAcceptedFoldBidirectionalCoordinates input fold).1
      (exactAcceptedFoldBidirectionalCoordinates input fold).2.1 attempt.1
  have returned : (replay actual).terminal =
      .returned (.completed (exactK12Runtime input)
        input.package.root.full.clientRun) := by
    exact exactBidirectionalFoldOneFoldRawReplay_actual_terminal transitionRoom
      programmedCover input fold
  have alphaExact : successfulDuplexOrdinaryValue actual =
      (exactK13ParsedProof input).schedule.alpha := by
    change successfulOrdinaryExactValue
        (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input
          fold) = (exactK13ParsedProof input).schedule.alpha
    exact (exactAcceptedFoldCoordinateRaw_value transitionRoom programmedCover
      input fold).trans source.alphaZeroExact.symm
  have scheduleExact : (exactK13ParsedProof input).schedule =
      scheduleAtAlpha (exactK13ParsedProof input).schedule
        (successfulDuplexOrdinaryValue actual) := by
    rw [alphaExact]
    exact (scheduleAtAlpha_original (exactK13ParsedProof input).schedule).symm
  exact plainRomReplayOracle_actualProof
    (words := words) (exactK13ParsedProof input).gamma
    (exactK13ParsedProof input).schedule
    (exactK13ParsedProof input).disclosedFinal replay actual
    (exactK12Runtime input) input.package.root.full.clientRun returned rfl
    scheduleExact

#print axioms exactAcceptedFoldReplayOracle
#print axioms exactAcceptedFoldReplayOracle_actualProof

end
end AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplayFilter
