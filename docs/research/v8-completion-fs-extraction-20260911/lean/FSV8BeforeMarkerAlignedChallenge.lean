import FSV8BeforeAlphaMarkerFactorization
import FSV8AlphaNonceBodyBridge
import FSV8AlignedAlphaChallengeRun
import FSV8V7WholeScriptAlignment

/-!
# From the same-body pre-marker run to the complete alpha challenge

This leaf removes the free aligned-marker premise from the successful live
alpha theorem.  It runs the source-shaped prefix that stops immediately after
response0, transports that exact run into the V7 oracle machine, constructs
the typed nonce from the same canonically parsed body, executes the real marker
query, and then constructs the complete one-to-four-pair alpha challenge.

The initial aligned verifier-entry state and successful before-marker run are
still explicit inputs.  Connecting those inputs to the exact whole-root run is
the next theorem.  This leaf assigns no probability.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 2400

namespace AspisV8Completion.FSV8BeforeMarkerAlignedChallenge

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8BeforeAlphaMarkerFactorization FSV8AlphaNonceBodyBridge
open FSV8AlignedAlphaSqueezeStep FSV8AlignedAlphaChallengeRun
open FSV8V7StateAlignment FSV8V7WholeScriptAlignment
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result
abbrev NonceBytes := AspisK1.V7Tag73TranscriptSchedule.NonceBytes

theorem run_next_le (tape : Tape) :
    forall {A : Type} {n : Nat} (script : Script Bytes Block A n)
      (state : State Bytes Block),
      (FSOracleExecution.run tape script state).2.next ≤ state.next + n := by
  intro A n script
  induction script with
  | done value => intro state; simp [FSOracleExecution.run]
  | abort => intro state; simp [FSOracleExecution.run]
  | @ask remaining input next ih =>
      intro state
      have tail := ih (query tape state input).1 (query tape state input).2
      have step := query_next_bound tape state input
      simp only [FSOracleExecution.run]
      omega

/-- Concrete evidence produced by one successful source prefix, its V7
execution, the same-body marker query, and the ensuing successful challenge.
All data are existentially constructed inside this proposition; no
conclusion-bearing structure is accepted as an input. -/
def ConstructedAlphaRun
    {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps) (limits : OracleLimits)
    (initialV7 : OracleState) (initialFS : State Bytes Block)
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (boundary : BeforeAlphaMarker out gamma body z)
    (limbs : List Nat) : Prop :=
  let script := beforeAlphaMarkerScript out gamma body z digest
  let beforeMachine := runMachine (controllerFromFreshAnswerTape finiteTape)
    limits .verifier beforeAlphaMarkerBudget initialV7
      (FSV8V7OracleMachineBridge.compileScript script)
  let beforeTranscript : Transcript :=
    { digest := boundary.digest
      oracle := (run tape script initialFS).2 }
  ∃ nonce : NonceBytes,
    List.ofFn nonce = FSLiveSelectedMiddleQueryRho.alpha0NonceBytes body ∧
    beforeMachine.halt = .returned (Except.ok boundary, boundary.digest) ∧
    ∃ marker : AlignedAlphaMarker tape finiteTape limits beforeMachine.oracle
        beforeTranscript nonce,
      let afterMarker := absorb tape beforeTranscript 20 (0 :: List.ofFn nonce)
      afterMarker = absorb tape beforeTranscript 20
          (0 :: FSLiveSelectedMiddleQueryRho.alpha0NonceBytes body) ∧
        (FSLiveChallengeTrace.challenge tape afterMarker).result = some limbs ∧
        SuccessfulAlignedChallenge tape finiteTape limits
          marker.afterMarker afterMarker
          (FSLiveChallengeTrace.challenge tape afterMarker).blocks
          (FSLiveChallengeTrace.challenge tape afterMarker).final
          (AspisK1.V7Tag73SamplerDecoder.encodeQm31Limbs limbs)

/-- A successful same-body prefix and live alpha result construct every
intermediate state.  The only source inputs are the actual prefix execution,
the canonical parse of that same `body`, and the live challenge result. -/
theorem successful_before_marker_then_alpha_constructs
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {initialV7 : OracleState}
    {initialFS : State Bytes Block}
    {out : OODResult} {gamma : K} {body : Bytes} {z : Fin 10 → K}
    {digest : Block} {boundary : BeforeAlphaMarker out gamma body z}
    {values : List K} {limbs : List Nat}
    (initialAligned : StateAligned tape finiteTape initialV7 initialFS)
    (bodyParsed : AspisV8.SameBodyChunkParser.fields
      (body.map UInt8.toFin) = some values)
    (totalRoom : initialV7.totalCalls + beforeAlphaMarkerBudget + 9 ≤
      limits.totalCalls)
    (freshRoom : initialV7.freshCalls + beforeAlphaMarkerBudget + 9 ≤
      limits.freshCalls)
    (tapeRoom : initialFS.next + beforeAlphaMarkerBudget + 9 ≤ steps)
    (prefixSuccess :
      (run tape (beforeAlphaMarkerScript out gamma body z digest) initialFS).1 =
        some (Except.ok boundary, boundary.digest))
    (liveSuccess :
      (FSLiveChallengeTrace.challenge tape
        (absorb tape
          { digest := boundary.digest
            oracle := (run tape
              (beforeAlphaMarkerScript out gamma body z digest) initialFS).2 }
          20 (0 :: FSLiveSelectedMiddleQueryRho.alpha0NonceBytes body))).result =
        some limbs) :
    ConstructedAlphaRun tape finiteTape limits initialV7 initialFS out gamma
      body z digest boundary limbs := by
  let script := beforeAlphaMarkerScript out gamma body z digest
  let beforeMachine := runMachine (controllerFromFreshAnswerTape finiteTape)
    limits .verifier beforeAlphaMarkerBudget initialV7
      (FSV8V7OracleMachineBridge.compileScript script)
  have alignedRun := run_compileScript_aligned limits .verifier script
    initialV7 initialFS initialAligned (by omega) (by omega) (by omega)
  have beforeHalt : beforeMachine.halt =
      .returned (Except.ok boundary, boundary.digest) := by
    have visible := alignedRun.1
    rw [prefixSuccess] at visible
    simpa [beforeMachine, script, ResultAligned] using visible
  have beforeAligned : StateAligned tape finiteTape beforeMachine.oracle
      (run tape script initialFS).2 := by
    simpa [beforeMachine] using alignedRun.2
  have callsBound := call_bound tape script initialFS
  have nextBound := run_next_le tape script initialFS
  have callsBound' :
      (run tape script initialFS).2.log.length ≤
        initialFS.log.length + beforeAlphaMarkerBudget := by
    simpa [script] using callsBound
  have nextBound' :
      (run tape script initialFS).2.next ≤
        initialFS.next + beforeAlphaMarkerBudget := by
    simpa [script] using nextBound
  have beforeTotalRoom : beforeMachine.oracle.totalCalls + 9 ≤
      limits.totalCalls := by
    rw [beforeAligned.totalCalls]
    rw [initialAligned.totalCalls] at totalRoom
    omega
  have beforeFreshRoom : beforeMachine.oracle.freshCalls + 9 ≤
      limits.freshCalls := by
    rw [beforeAligned.freshCalls]
    rw [initialAligned.freshCalls] at freshRoom
    omega
  have beforeTapeRoom : (run tape script initialFS).2.next + 9 ≤ steps := by
    omega
  let nonce := alpha0NonceOfBody body
  have nonceBytes : List.ofFn nonce =
      FSLiveSelectedMiddleQueryRho.alpha0NonceBytes body :=
    alpha0NonceOfBody_ofFn body (bodyRoom_of_fields_success body values bodyParsed)
  let beforeTranscript : Transcript :=
    { digest := boundary.digest
      oracle := (run tape script initialFS).2 }
  have beforeAlignedTranscript : StateAligned tape finiteTape
      beforeMachine.oracle beforeTranscript.oracle := by
    simpa [beforeTranscript] using beforeAligned
  have beforeTranscriptTapeRoom : beforeTranscript.oracle.next + 9 ≤ steps := by
    simpa [beforeTranscript] using beforeTapeRoom
  let marker := alignedAlphaMarker_complete (limits := limits)
    (s := beforeTranscript) nonce
    beforeAlignedTranscript
    (by omega) (by omega) (by omega)
  let afterMarker := absorb tape beforeTranscript 20 (0 :: List.ofFn nonce)
  have sameBodyMarker : afterMarker = absorb tape beforeTranscript 20
      (0 :: FSLiveSelectedMiddleQueryRho.alpha0NonceBytes body) := by
    dsimp [afterMarker]
    rw [nonceBytes]
  have liveTyped :
      (FSLiveChallengeTrace.challenge tape afterMarker).result = some limbs := by
    rw [sameBodyMarker]
    simpa [beforeTranscript, script] using liveSuccess
  have afterTotal : marker.afterMarker.totalCalls + 8 ≤ limits.totalCalls := by
    rw [marker.aligned.totalCalls]
    have logStep := FSV8AlignedAlphaSqueezeStep.query_log_length tape
      beforeTranscript.oracle (alphaMarkerInput beforeTranscript nonce)
    simpa [afterMarker, FSBoundedTranscript.absorb, alphaMarkerInput] using
      (show (FSOracleExecution.query tape beforeTranscript.oracle
          (alphaMarkerInput beforeTranscript nonce)).2.log.length + 8 ≤
          limits.totalCalls by
        rw [logStep]
        change (run tape script initialFS).2.log.length + 1 + 8 ≤ _
        rw [← beforeAligned.totalCalls]
        omega)
  have afterFresh : marker.afterMarker.freshCalls + 8 ≤ limits.freshCalls := by
    rw [marker.aligned.freshCalls]
    have step := query_next_bound tape beforeTranscript.oracle
      (alphaMarkerInput beforeTranscript nonce)
    change (FSOracleExecution.query tape beforeTranscript.oracle
      (alphaMarkerInput beforeTranscript nonce)).2.next + 8 ≤ _
    have startFresh : beforeTranscript.oracle.next + 9 ≤
        limits.freshCalls := by
      change (run tape script initialFS).2.next + 9 ≤ _
      rw [← beforeAligned.freshCalls]
      exact beforeFreshRoom
    omega
  have afterTape : afterMarker.oracle.next + 8 ≤ steps := by
    have step := query_next_bound tape beforeTranscript.oracle
      (alphaMarkerInput beforeTranscript nonce)
    change (FSOracleExecution.query tape beforeTranscript.oracle
      (alphaMarkerInput beforeTranscript nonce)).2.next + 8 ≤ _
    have room := beforeTranscriptTapeRoom
    omega
  have challenge := successful_live_challenge_constructs_aligned_run
    marker.aligned marker.prefixPath afterTotal afterFresh afterTape liveTyped
  unfold ConstructedAlphaRun
  dsimp only
  exact ⟨nonce, nonceBytes, beforeHalt, marker, sameBodyMarker, liveTyped,
    challenge⟩

#print axioms run_next_le
#print axioms successful_before_marker_then_alpha_constructs

end
end AspisV8Completion.FSV8BeforeMarkerAlignedChallenge
