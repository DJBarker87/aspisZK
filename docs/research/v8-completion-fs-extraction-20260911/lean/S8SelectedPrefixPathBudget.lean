import S8SemanticPathBudget
import FSV8S7SelectedSourcePrefixBudget

/-!
# Path-sensitive selected prefix call budget

This file derives the advertised 420-call bound through the selected alpha0
draw from the executable branches.  In particular, the OOD `3 x 3` retry
shape and the row/image retry loops are proved here rather than supplied as
the numerical inventory `22 ordinary draws + 10 absorbs`.

The 420 bound is deliberately only for the chronological prefix through
alpha0; it is not a bound for the later query/relation suffix of the complete
verifier.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace AspisV8Completion.S8SelectedPrefixPathBudget

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSOODSampler FSNonzeroQM31
open FSV7OODSampler FSV8OODBodyScript FSV7OODBodyScript FSV8PostOODGammaScript
open FSV8BeforeAlphaMarkerFactorization
open FSV8S5SelectedVerifierCallbacks FSV8S7SelectedSourcePrefixBudget
open S8BufferedPotential S8SemanticPathBudget
open SameBodyFunctionalProducerSource FSLiveSourceFunctionalMiddle
open FSLiveSelectedMiddleQueryRho

abbrev Bytes := List UInt8
abbrev HB := FSBoundedTranscript.Block

noncomputable section
local instance : DecidableEq FSV7OODBodyScript.Point := Classical.decEq _

theorem challengeScript_logBound (tape : FSBoundedTranscript.Tape) (digest : HB) :
    LogBound tape (challengeScript digest) 8 := by
  intro oracle
  let start : FSBoundedTranscript.Transcript := ⟨digest, oracle⟩
  simpa only [start] using
    S8BufferedPotential.source_challengeScript_log_length_le_eight tape start

theorem logBound_abort (tape : FSBoundedTranscript.Tape) {A : Type} {n cost : Nat} :
    LogBound tape (.abort : Script Bytes HB A n) cost := by
  intro oracle
  simp only [run]
  omega

theorem logBound_bind_done (tape : FSBoundedTranscript.Tape)
    {A B : Type} {n cost : Nat} (script : Script Bytes HB A n)
    (next : A → B) (bound : LogBound tape script cost) :
    LogBound tape (bind script fun value => .done (n := 0) (next value)) cost := by
  simpa only [Nat.add_zero] using
    logBound_bind tape script (fun value => .done (n := 0) (next value)) bound
      (fun value => logBound_done tape (next value))

theorem circleScript_logBound (tape : FSBoundedTranscript.Tape) {Point : Type}
    (decode : List Nat → Option Point) : ∀ n digest,
    LogBound tape (circleScript decode n digest) (8 * n) := by
  intro n
  induction n with
  | zero =>
      intro digest
      simpa only [circleScript, Nat.mul_zero] using
        logBound_done tape
          ((Except.error FSOODSampler.Error.parameterExhausted :
            Except FSOODSampler.Error Point), digest)
  | succ n ih =>
      intro digest
      simp only [circleScript]
      rw [show 8 * (n + 1) = 8 + 8 * n by omega]
      apply logBound_bind tape _ _ (challengeScript_logBound tape digest)
      intro draw
      cases hdraw : draw.1 with
      | none =>
          simp only [hdraw]
          exact logBound_done_cost tape
            ((Except.error FSOODSampler.Error.limbExhausted :
              Except FSOODSampler.Error Point), draw.2)
            (8 * n)
      | some limbs =>
          simp only [hdraw]
          cases hdecode : decode limbs with
          | none =>
              simp only [hdecode]
              exact ih draw.2
          | some point =>
              simp only [hdecode]
              exact logBound_done_cost tape
                ((Except.ok point : Except FSOODSampler.Error Point), draw.2)
                (8 * n)

theorem distinctScript_logBound (tape : FSBoundedTranscript.Tape) {Point : Type}
    [DecidableEq Point] (decode : List Nat → Option Point) (first : Point) :
    ∀ n digest, LogBound tape (distinctScript decode first n digest) (24 * n) := by
  intro n
  induction n with
  | zero =>
      intro digest
      simpa only [distinctScript, Nat.mul_zero] using
        logBound_done tape
          ((Except.error FSOODSampler.Error.distinctExhausted :
            Except FSOODSampler.Error Point), digest)
  | succ n ih =>
      intro digest
      simp only [distinctScript]
      rw [show 24 * (n + 1) = 24 + 24 * n by omega]
      apply logBound_bind tape _ _ (circleScript_logBound tape decode 3 digest)
      intro draw
      cases hdraw : draw.1 with
      | error error =>
          simp only [hdraw]
          exact logBound_done_cost tape
            ((Except.error error : Except FSOODSampler.Error Point), draw.2)
            (24 * n)
      | ok point =>
          simp only [hdraw]
          split <;> rename_i heq
          · exact ih draw.2
          · exact logBound_done_cost tape
              ((Except.ok point : Except FSOODSampler.Error Point), draw.2)
              (24 * n)

theorem sourceReadOnlyFirst_logBound (tape : FSBoundedTranscript.Tape)
    (point : FSV7OODBodyScript.Point) :
    LogBound tape (sourceReadOnlyFirst point) 0 :=
  logBound_done tape ()

theorem sourceReadOnlySecond_logBound (tape : FSBoundedTranscript.Tape)
    (first second : FSV7OODBodyScript.Point) :
    LogBound tape (sourceReadOnlySecond first second) 0 :=
  logBound_done tape ()

theorem answerScript_readOnly_logBound (tape : FSBoundedTranscript.Tape)
    (point : FSV7OODBodyScript.Point) (body : Bytes) (sample : Fin 2) :
    LogBound tape (answerScript sourceReadOnlyFirst point body sample) 0 := by
  apply logBound_map
  exact sourceReadOnlyFirst_logBound tape point

theorem selected_afterSecond_logBound_1
    (firstPoint : FSV7OODBodyScript.Point) (afterFirst : HB)
    (body : Bytes)
    (secondDraw : Except FSOODSampler.Error FSV7OODBodyScript.Point × HB)
    (tape : FSBoundedTranscript.Tape) :
    LogBound tape
      (afterSecond firstPoint afterFirst sourceReadOnlySecond body secondDraw) 1 := by
  unfold afterSecond
  cases hsecond : secondDraw.1 with
  | error error =>
      simp only [hsecond]
      exact logBound_done_cost tape _ 1
  | ok secondPoint =>
      simp only [hsecond]
      intro oracle
      simp only [run_bind, run_answerScript, run_sourceReadOnlySecond,
        Option.map_some, Prod.fst, Prod.snd, absorbScript, run,
        S8BufferedPotential.query_log_length]
      omega

/- The selected read-only OOD source performs at most 98 calls on every
branch: `3*8`, one first-row absorb, `3*(3*8)`, one second-row absorb. -/
theorem selected_ood_source_logBound_98 (body : Bytes) (digest : HB)
    (tape : FSBoundedTranscript.Tape) :
    LogBound tape
      (FSV7OODBodyScript.sourceScript sourceReadOnlyFirst sourceReadOnlySecond
        body digest) 98 := by
  unfold FSV7OODBodyScript.sourceScript checkedBodyPairScript
  split
  · unfold bodyPairScript
    rw [show (98 : Nat) = 24 + 74 by decide]
    apply logBound_bind tape _ _ (circleScript_logBound tape decodePoint 3 digest)
    intro firstDraw
    cases firstDraw.1 with
    | error error => exact logBound_done_cost tape _ 74
    | ok firstPoint =>
      rw [show (74 : Nat) = 0 + 74 by decide]
      apply logBound_bind tape _ _
        (answerScript_readOnly_logBound tape firstPoint body 0)
      intro firstAnswer
      rw [show (74 : Nat) = 1 + 73 by decide]
      apply logBound_bind tape _ _
        (absorbScript_logBound tape firstDraw.2 62 (0 :: firstAnswer))
      intro afterFirst
      rw [show (73 : Nat) = 72 + 1 by decide]
      apply logBound_bind tape _ _
        (distinctScript_logBound tape decodePoint firstPoint 3 afterFirst)
      intro secondDraw
      exact selected_afterSecond_logBound_1 firstPoint afterFirst body secondDraw tape
  · exact logBound_abort tape

/- OOD rows plus batch nonce and gamma: 98 + 1 + 3*8 = 123. -/
theorem selected_sourceThenGamma_logBound_123 (body : Bytes) (digest : HB)
    (tape : FSBoundedTranscript.Tape) :
    LogBound tape
      (sourceThenGammaScript sourceReadOnlyFirst sourceReadOnlySecond body digest)
      123 := by
  unfold sourceThenGammaScript
  rw [show (123 : Nat) = 98 + 25 by decide]
  apply logBound_bind tape _ _ (selected_ood_source_logBound_98 body digest tape)
  intro source
  cases source.1 with
  | error error => exact logBound_done_cost tape _ 25
  | ok out =>
      rw [show (25 : Nat) = 1 + 24 by decide]
      apply logBound_bind tape _ _
        (absorbScript_logBound tape source.2 28 (batchNonceBytes body))
      intro afterNonce
      rw [show (24 : Nat) = 24 + 0 by decide]
      apply logBound_bind tape _ _
        (nonzeroScript_logBound tape 3 afterNonce)
      intro gamma
      exact logBound_done tape _

theorem afterFunctionalBeforeMarkerScript_logBound_28
    (out : FSV7OODBodyScript.Result) (gamma : FSNonzeroQM31.K)
    (body : Bytes) (z : Fin 10 → FSNonzeroQM31.K)
    (kappa : FSNonzeroQM31.K) (functional : Encoded)
    (functionalRun : fromInputs out gamma kappa body z = some functional)
    (digest : HB) (tape : FSBoundedTranscript.Tape) :
    LogBound tape
      (afterFunctionalBeforeMarkerScript out gamma body z kappa functional
        functionalRun digest) 28 := by
  unfold afterFunctionalBeforeMarkerScript
  rw [show (28 : Nat) = 1 + 27 by decide]
  apply logBound_bind tape _ _
    (absorbScript_logBound tape digest 1 functional.description)
  intro afterDescription
  rw [show (27 : Nat) = 1 + 26 by decide]
  apply logBound_bind tape _ _
    (absorbScript_logBound tape afterDescription 6 functional.claim)
  intro afterClaim
  rw [show (26 : Nat) = 1 + 25 by decide]
  apply logBound_bind tape _ _
    (absorbScript_logBound tape afterClaim 1 compactFunctionalProfile)
  intro afterProfile
  rw [show (25 : Nat) = 24 + 1 by decide]
  apply logBound_bind tape _ _ (nonzeroScript_logBound tape 3 afterProfile)
  intro tauDraw
  cases htau : tauDraw.1 with
  | error error =>
      simp only [htau]
      exact logBound_done_cost tape _ 1
  | ok tau =>
      simp only [htau]
      exact logBound_bind_done tape _
        (fun afterResponse0 =>
          (Except.ok
              ({ kappa := kappa
                 tau := tau
                 functional := functional
                 functionalRun := functionalRun
                 digest := afterResponse0 } :
                BeforeAlphaMarker out gamma body z),
            afterResponse0))
        (absorbScript_logBound tape tauDraw.2 52 (0 :: response0Bytes body))

theorem alphaMarkerContinuation_logBound_1
    (out : FSV7OODBodyScript.Result) (gamma : FSNonzeroQM31.K)
    (body : Bytes) (z : Fin 10 → FSNonzeroQM31.K)
    (boundary : BeforeAlphaMarker out gamma body z)
    (tape : FSBoundedTranscript.Tape) :
    LogBound tape (alphaMarkerContinuation out gamma body z boundary) 1 := by
  unfold alphaMarkerContinuation
  exact logBound_bind_done tape _
    (fun afterAlphaNonce =>
      (Except.ok
          ({ kappa := boundary.kappa
             tau := boundary.tau
             functional := boundary.functional
             functionalRun := boundary.functionalRun
             digest := afterAlphaNonce } :
            FSV8ExecutablePreAlphaFactorization.PreAlpha out gamma body z),
        afterAlphaNonce))
    (absorbScript_logBound tape boundary.digest 20 (0 :: alpha0NonceBytes body))

/- The carried row/image stage has five literal absorbs and two three-attempt
nonzero draws, hence at most 53 calls. -/
theorem beforeAlphaMarkerScript_logBound_53
    (out : FSV7OODBodyScript.Result) (gamma : FSNonzeroQM31.K) (body : Bytes)
    (z : Fin 10 → FSNonzeroQM31.K) (digest : HB)
    (tape : FSBoundedTranscript.Tape) :
    LogBound tape (beforeAlphaMarkerScript out gamma body z digest) 53 := by
  unfold beforeAlphaMarkerScript
  rw [show (53 : Nat) = 1 + 52 by decide]
  apply logBound_bind tape _ _
    (absorbScript_logBound tape digest 50 (inactiveClaimBytes body))
  intro afterInactive
  rw [show (52 : Nat) = 24 + 28 by decide]
  apply logBound_bind tape _ _ (nonzeroScript_logBound tape 3 afterInactive)
  intro kappaDraw
  cases hkappa : kappaDraw.1 with
  | error error =>
      simp only [hkappa]
      exact logBound_done_cost tape _ 28
  | ok kappa =>
      simp only [hkappa]
      split
      · exact logBound_done_cost tape _ 28
      · rename_i functionalRun functional
        exact afterFunctionalBeforeMarkerScript_logBound_28 out gamma body z kappa
          functionalRun functional kappaDraw.2 tape

theorem selectedBeforeMarkerScript_logBound_176 (body : Bytes)
    (z : Fin 10 → FSNonzeroQM31.K) (digest : HB)
    (tape : FSBoundedTranscript.Tape) :
    LogBound tape (selectedBeforeMarkerScript body z digest) 176 := by
  unfold selectedBeforeMarkerScript
  rw [show (176 : Nat) = 123 + 53 by decide]
  apply logBound_bind tape _ _
    (selected_sourceThenGamma_logBound_123 body digest tape)
  intro source
  cases source.1 with
  | error error => exact logBound_done_cost tape _ 53
  | ok pair =>
      rcases pair with ⟨out, gamma⟩
      intro oracle
      rw [run_map]
      exact beforeAlphaMarkerScript_logBound_53 out gamma body z source.2 tape oracle

theorem selectedRelaxedThroughBeforeMarkerScript_logBound_411
    (binding : FSLiveSemanticPrefix.Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) :
    LogBound tape
      (selectedRelaxedThroughBeforeMarkerScript true binding body) 411 := by
  unfold selectedRelaxedThroughBeforeMarkerScript
  rw [show (411 : Nat) = 234 + 177 by decide]
  apply logBound_bind tape _ _
    (selected_semanticScript_logBound_234 binding body tape)
  intro semanticResult
  cases semanticResult with
  | error error => exact logBound_done_cost tape _ 177
  | ok semantic =>
      rw [show (177 : Nat) = 1 + 176 by decide]
      apply logBound_bind tape _ _
        (absorbScript_logBound tape semantic.finalDigest 49 (pointClaimBytes body))
      intro afterPoints
      intro oracle
      rw [run_map]
      exact selectedBeforeMarkerScript_logBound_176 body semantic.z afterPoints tape oracle

/- The actual selected prefix after semantic execution costs at most 186:
point claims 1, selected OOD/gamma/row/image 176, marker 1, alpha0 8. -/
theorem selectedRelaxedThroughAlphaScript_logBound_420
    (binding : FSLiveSemanticPrefix.Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) :
    LogBound tape (selectedRelaxedThroughAlphaScript true binding body) 420 := by
  unfold selectedRelaxedThroughAlphaScript
  rw [show (420 : Nat) = 411 + 9 by decide]
  apply logBound_bind tape _ _
    (selectedRelaxedThroughBeforeMarkerScript_logBound_411 binding body tape)
  intro prefixResult
  cases prefixResult.1 with
  | error error => exact logBound_done_cost tape _ 9
  | ok prefixValue =>
      rw [show (9 : Nat) = 1 + 8 by decide]
      apply logBound_bind tape _ _
        (alphaMarkerContinuation_logBound_1 prefixValue.before.out
          prefixValue.before.gamma body prefixValue.semantic.z
          prefixValue.before.boundary tape)
      intro markerResult
      cases markerResult.1 with
      | error error => exact logBound_done_cost tape _ 8
      | ok preAlpha =>
          apply logBound_map
          exact candidateScript_logBound tape markerResult.2

theorem selectedRelaxedThroughAlpha_log_length_le_420
    (binding : FSLiveSemanticPrefix.Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape)
    (oracle : Oracle) :
    (run tape (selectedRelaxedThroughAlphaScript true binding body) oracle).2.log.length
      ≤ oracle.log.length + 420 :=
  selectedRelaxedThroughAlphaScript_logBound_420 binding body tape oracle

#print axioms selected_ood_source_logBound_98
#print axioms selected_sourceThenGamma_logBound_123
#print axioms beforeAlphaMarkerScript_logBound_53
#print axioms selectedRelaxedThroughAlpha_log_length_le_420

end
end AspisV8Completion.S8SelectedPrefixPathBudget
