import FSV8ExecutablePreAlphaFactorization
import FSV8CompileScriptAlgebra

/-!
# Executable factorization immediately before the alpha0 marker

The existing pre-alpha factorization returns after absorbing the alpha0 nonce.
This leaf exposes the immediately preceding boundary instead.  The returned
`BeforeAlphaMarker` is produced by the same execution and carries the digest
after response0.  Its continuation absorbs `alpha0NonceBytes body` from the
same dependent `body`, then constructs the existing `PreAlpha` value.

The two final theorems preserve both the finite interpreter result/oracle and
the compiled oracle-machine syntax.  They make no freshness, alignment, or
probability claim.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8BeforeAlphaMarkerFactorization

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31
open FSLiveSelectedMiddleQueryRho
open SameBodyFunctionalProducerSource
open FSLiveSourceFunctionalMiddle
open FSV8V7OracleMachineBridge
open FSV8ExecutablePreAlphaFactorization
open FSV8CompileScriptAlgebra
open AspisK1.V7Tag73SharedOracleVerifierRunner

noncomputable section

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

abbrev beforeAlphaMarkerBudget : Nat := 401
abbrev afterFunctionalBeforeMarkerBudget : Nat := 202

/-- Values fixed immediately after response0 and before the alpha0 nonce
absorption.  The nonce remains a deterministic slice of the indexed `body`;
it is not copied into this structure as an independent input. -/
structure BeforeAlphaMarker (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) where
  kappa : K
  tau : K
  functional : Encoded
  functionalRun : fromInputs out gamma kappa body z = some functional
  digest : Block

/-- Execute the successful-functional suffix through response0, stopping one
literal oracle query before the existing `PreAlpha` boundary. -/
def afterFunctionalBeforeMarkerScript (out : OODResult) (gamma : K)
    (body : Bytes) (z : Fin 10 → K) (kappa : K)
    (functional : Encoded)
    (functionalRun : fromInputs out gamma kappa body z = some functional)
    (digest : Block) :
    Script Bytes Block
      (Except FSLiveSourceFunctionalMiddle.Error
        (BeforeAlphaMarker out gamma body z) × Block)
      afterFunctionalBeforeMarkerBudget :=
  bind (m := 201) (absorbScript digest 1 functional.description)
      fun afterDescription =>
    bind (m := 200) (absorbScript afterDescription 6 functional.claim)
        fun afterClaim =>
      bind (m := 199) (absorbScript afterClaim 1 compactFunctionalProfile)
          fun afterImageProfile =>
        bind (m := 1) (nonzeroScript 3 afterImageProfile) fun tauDraw =>
          match tauDraw.1 with
          | .error e => .done
              (Except.error (FSLiveSourceFunctionalMiddle.Error.tau e),
                tauDraw.2)
          | .ok tau =>
            bind (m := 0)
                (absorbScript tauDraw.2 52 (0 :: response0Bytes body))
              fun afterResponse0 =>
                .done
                  (Except.ok
                    { kappa := kappa
                      tau := tau
                      functional := functional
                      functionalRun := functionalRun
                      digest := afterResponse0 },
                    afterResponse0)

/-- Existing pre-alpha prefix, stopped immediately before the alpha0 marker. -/
def beforeAlphaMarkerScript (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (digest : Block) :
    Script Bytes Block
      (Except FSLiveSourceFunctionalMiddle.Error
        (BeforeAlphaMarker out gamma body z) × Block)
      beforeAlphaMarkerBudget :=
  bind (m := 400) (absorbScript digest 50 (inactiveClaimBytes body))
      fun afterInactive =>
    bind (m := afterFunctionalBeforeMarkerBudget)
        (nonzeroScript 3 afterInactive) fun kappaDraw =>
      match kappaDraw.1 with
      | .error e => .done
          (Except.error (FSLiveSourceFunctionalMiddle.Error.kappa e),
            kappaDraw.2)
      | .ok kappa =>
        match functionalRun : fromInputs out gamma kappa body z with
        | none => .done
            (Except.error FSLiveSourceFunctionalMiddle.Error.functional,
              kappaDraw.2)
        | some functional =>
          afterFunctionalBeforeMarkerScript out gamma body z kappa functional
            functionalRun kappaDraw.2

/-- The one-query continuation uses the same indexed body as the preceding
boundary. -/
def alphaMarkerContinuation (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (boundary : BeforeAlphaMarker out gamma body z) :
    Script Bytes Block
      (Except FSLiveSourceFunctionalMiddle.Error
        (PreAlpha out gamma body z) × Block) 1 :=
  bind (m := 0)
      (absorbScript boundary.digest 20 (0 :: alpha0NonceBytes body))
    fun afterAlphaNonce =>
      .done
        (Except.ok
          { kappa := boundary.kappa
            tau := boundary.tau
            functional := boundary.functional
            functionalRun := boundary.functionalRun
            digest := afterAlphaNonce },
          afterAlphaNonce)

/-- Exact interpreter result of the literal one-query marker continuation.
This exposes both the returned digest and final oracle from the same absorb. -/
theorem run_alphaMarkerContinuation
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (boundary : BeforeAlphaMarker out gamma body z)
    (tape : Tape) (oracle : Oracle) :
    let afterMarker := absorb tape
      ({ digest := boundary.digest, oracle := oracle } :
        FSBoundedTranscript.Transcript)
      20 (0 :: alpha0NonceBytes body)
    run tape (alphaMarkerContinuation out gamma body z boundary) oracle =
      (some
        (Except.ok
          { kappa := boundary.kappa
            tau := boundary.tau
            functional := boundary.functional
            functionalRun := boundary.functionalRun
            digest := afterMarker.digest },
          afterMarker.digest),
        afterMarker.oracle) := by
  let start : FSBoundedTranscript.Transcript :=
    { digest := boundary.digest, oracle := oracle }
  let afterMarker := absorb tape start 20 (0 :: alpha0NonceBytes body)
  have markerRun :
      run tape (absorbScript boundary.digest 20
        (0 :: alpha0NonceBytes body)) oracle =
        (some afterMarker.digest, afterMarker.oracle) := by
    exact run_absorb tape start 20 (0 :: alpha0NonceBytes body)
  dsimp only
  unfold alphaMarkerContinuation
  rw [run_bind]
  simp only [markerRun, Prod.fst, Prod.snd, FSOracleExecution.run]
  rfl

/-- Rejoin the before-marker prefix and literal marker continuation. -/
def factoredPreAlphaScript (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (digest : Block) :
    Script Bytes Block
      (Except FSLiveSourceFunctionalMiddle.Error
        (PreAlpha out gamma body z) × Block) preAlphaBudget :=
  bind (m := 1) (beforeAlphaMarkerScript out gamma body z digest)
    fun boundaryDraw =>
      match boundaryDraw.1 with
      | .error e => .done (Except.error e, boundaryDraw.2)
      | .ok boundary => alphaMarkerContinuation out gamma body z boundary

private theorem successful_afterFunctionalBeforeMarker_digest
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (kappa : K) (functional : Encoded)
    (functionalRun : fromInputs out gamma kappa body z = some functional)
    (digest : Block) (tape : Tape) (oracle : Oracle)
    (before : BeforeAlphaMarker out gamma body z) (returnedDigest : Block)
    (success :
      (run tape
        (afterFunctionalBeforeMarkerScript out gamma body z kappa functional
          functionalRun digest) oracle).1 =
        some (Except.ok before, returnedDigest)) :
    returnedDigest = before.digest := by
  let s0 : FSBoundedTranscript.Transcript := ⟨digest, oracle⟩
  let s1 := absorb tape s0 1 functional.description
  have h1 : run tape (absorbScript digest 1 functional.description) oracle =
      (some s1.digest, s1.oracle) := by
    exact run_absorb tape
      ({ digest := digest, oracle := oracle } : FSBoundedTranscript.Transcript)
      1 functional.description
  unfold afterFunctionalBeforeMarkerScript at success
  rw [run_bind] at success
  simp only [h1, Prod.fst, Prod.snd] at success
  let s2 := absorb tape s1 6 functional.claim
  have h2 : run tape (absorbScript s1.digest 6 functional.claim) s1.oracle =
      (some s2.digest, s2.oracle) := run_absorb _ _ _ _
  rw [run_bind] at success
  simp only [h2, Prod.fst, Prod.snd] at success
  let s3 := absorb tape s2 1 compactFunctionalProfile
  have h3 : run tape (absorbScript s2.digest 1 compactFunctionalProfile)
      s2.oracle = (some s3.digest, s3.oracle) := run_absorb _ _ _ _
  rw [run_bind] at success
  simp only [h3, Prod.fst, Prod.snd] at success
  rw [run_bind, FSNonzeroQM31.run_nonzero] at success
  simp only [Prod.fst, Prod.snd] at success
  cases tauResult : (FSNonzeroQM31.nonzero tape 3 s3).1 with
  | error e => simp [tauResult, run] at success
  | ok tau =>
      simp only [tauResult] at success
      let s4 := absorb tape (FSNonzeroQM31.nonzero tape 3 s3).2 52
        (0 :: response0Bytes body)
      have h4 : run tape
          (absorbScript (FSNonzeroQM31.nonzero tape 3 s3).2.digest 52
            (0 :: response0Bytes body))
          (FSNonzeroQM31.nonzero tape 3 s3).2.oracle =
          (some s4.digest, s4.oracle) := run_absorb _ _ _ _
      rw [run_bind] at success
      simp only [h4, Prod.fst, Prod.snd, run, Option.some.injEq,
        Prod.mk.injEq, Except.ok.injEq] at success
      exact success.2.symm.trans
        (congrArg BeforeAlphaMarker.digest success.1)

/-- A successful before-marker prefix returns the digest stored in the
boundary it has just constructed; the two values are not independent. -/
theorem successful_beforeAlphaMarker_digest
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (tape : Tape) (oracle : Oracle)
    (before : BeforeAlphaMarker out gamma body z) (returnedDigest : Block)
    (success :
      (run tape (beforeAlphaMarkerScript out gamma body z digest) oracle).1 =
        some (Except.ok before, returnedDigest)) :
    returnedDigest = before.digest := by
  let s0 : FSBoundedTranscript.Transcript := ⟨digest, oracle⟩
  let s1 := absorb tape s0 50 (inactiveClaimBytes body)
  have h1 : run tape (absorbScript digest 50 (inactiveClaimBytes body)) oracle =
      (some s1.digest, s1.oracle) := by
    exact run_absorb tape
      ({ digest := digest, oracle := oracle } : FSBoundedTranscript.Transcript)
      50 (inactiveClaimBytes body)
  unfold beforeAlphaMarkerScript at success
  rw [run_bind] at success
  simp only [h1, Prod.fst, Prod.snd] at success
  rw [run_bind, FSNonzeroQM31.run_nonzero] at success
  simp only [Prod.fst, Prod.snd] at success
  cases kappaResult : (FSNonzeroQM31.nonzero tape 3 s1).1 with
  | error e => simp [kappaResult, run] at success
  | ok kappa =>
      simp only [kappaResult] at success
      split at success
      · simp [run] at success
      · rename_i functional functionalRun
        exact successful_afterFunctionalBeforeMarker_digest out gamma body z
          kappa functional functionalRun
          (FSNonzeroQM31.nonzero tape 3 s1).2.digest tape
          (FSNonzeroQM31.nonzero tape 3 s1).2.oracle before returnedDigest
          success

private theorem run_afterFunctional_before_marker_factor
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (kappa : K) (functional : Encoded)
    (functionalRun : fromInputs out gamma kappa body z = some functional)
    (digest : Block) (tape : Tape) (oracle : Oracle) :
    run tape
        (bind (m := 1)
          (afterFunctionalBeforeMarkerScript out gamma body z kappa functional
            functionalRun digest) fun boundaryDraw =>
          match boundaryDraw.1 with
          | .error e => .done (Except.error e, boundaryDraw.2)
          | .ok boundary =>
              alphaMarkerContinuation out gamma body z boundary)
        oracle =
      run tape
        (afterFunctionalPreAlphaScript out gamma body z kappa functional
          functionalRun digest) oracle := by
  let s0 : FSBoundedTranscript.Transcript := ⟨digest, oracle⟩
  let s1 := absorb tape s0 1 functional.description
  have h1 : run tape (absorbScript digest 1 functional.description) oracle =
      (some s1.digest, s1.oracle) := by
    exact run_absorb tape
      ({ digest := digest, oracle := oracle } : FSBoundedTranscript.Transcript)
      1 functional.description
  unfold afterFunctionalBeforeMarkerScript
    afterFunctionalPreAlphaScript alphaMarkerContinuation
  rw [run_bind]
  simp only [run_bind, h1, Prod.fst, Prod.snd]
  let s2 := absorb tape s1 6 functional.claim
  have h2 : run tape (absorbScript s1.digest 6 functional.claim) s1.oracle =
      (some s2.digest, s2.oracle) := run_absorb _ _ _ _
  simp only [h2, Prod.fst, Prod.snd]
  let s3 := absorb tape s2 1 compactFunctionalProfile
  have h3 : run tape (absorbScript s2.digest 1 compactFunctionalProfile)
      s2.oracle = (some s3.digest, s3.oracle) := run_absorb _ _ _ _
  simp only [h3, Prod.fst, Prod.snd]
  have ht := FSNonzeroQM31.run_nonzero tape 3 s3
  simp only [ht, Prod.fst, Prod.snd]
  cases tauResult : (FSNonzeroQM31.nonzero tape 3 s3).1 with
  | error e => simp [tauResult, run]
  | ok tau =>
      simp only [tauResult]
      let s4 := absorb tape (FSNonzeroQM31.nonzero tape 3 s3).2 52
        (0 :: response0Bytes body)
      have h4 : run tape
          (absorbScript (FSNonzeroQM31.nonzero tape 3 s3).2.digest 52
            (0 :: response0Bytes body))
          (FSNonzeroQM31.nonzero tape 3 s3).2.oracle =
          (some s4.digest, s4.oracle) := run_absorb _ _ _ _
      rw [run_bind, h4]
      simp only [Prod.fst, Prod.snd, run]
      rfl

private theorem run_afterKappa_before_marker_factor
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (kappa : K) (digest : Block) (tape : Tape) (oracle : Oracle) :
    run tape
        (bind (m := 1)
          (match functionalRun : fromInputs out gamma kappa body z with
          | none => .done
              (Except.error FSLiveSourceFunctionalMiddle.Error.functional,
                digest)
          | some functional =>
              afterFunctionalBeforeMarkerScript out gamma body z kappa
                functional functionalRun digest) fun boundaryDraw =>
          match boundaryDraw.1 with
          | .error e => .done (Except.error e, boundaryDraw.2)
          | .ok boundary => alphaMarkerContinuation out gamma body z boundary)
        oracle =
      run tape
        (match functionalRun : fromInputs out gamma kappa body z with
        | none => .done
            (Except.error FSLiveSourceFunctionalMiddle.Error.functional,
              digest)
        | some functional =>
            afterFunctionalPreAlphaScript out gamma body z kappa functional
              functionalRun digest)
        oracle := by
  split
  · simp [run_bind, run]
  · rename_i functional functionalRun
    exact run_afterFunctional_before_marker_factor out gamma body z kappa
      functional functionalRun digest tape oracle

/-- Splitting immediately before the alpha marker preserves the interpreter's
complete result and final oracle for every tape and entry state. -/
theorem run_factoredPreAlphaScript_eq_preAlphaScript
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (tape : Tape) (oracle : Oracle) :
    run tape (factoredPreAlphaScript out gamma body z digest) oracle =
      run tape (preAlphaScript out gamma body z digest) oracle := by
  let s0 : FSBoundedTranscript.Transcript := ⟨digest, oracle⟩
  let s1 := absorb tape s0 50 (inactiveClaimBytes body)
  have h1 : run tape (absorbScript digest 50 (inactiveClaimBytes body)) oracle =
      (some s1.digest, s1.oracle) := by
    exact run_absorb tape
      ({ digest := digest, oracle := oracle } : FSBoundedTranscript.Transcript)
      50 (inactiveClaimBytes body)
  unfold factoredPreAlphaScript beforeAlphaMarkerScript preAlphaScript
  rw [run_bind]
  simp only [run_bind, h1, Prod.fst, Prod.snd]
  have hk := FSNonzeroQM31.run_nonzero tape 3 s1
  simp only [hk, Prod.fst, Prod.snd]
  cases kappaResult : (FSNonzeroQM31.nonzero tape 3 s1).1 with
  | error e => simp [kappaResult, run]
  | ok kappa =>
      simp only [kappaResult]
      rw [← run_bind]
      exact run_afterKappa_before_marker_factor out gamma body z kappa
        (FSNonzeroQM31.nonzero tape 3 s1).2.digest tape
        (FSNonzeroQM31.nonzero tape 3 s1).2.oracle

private theorem compile_afterFunctional_before_marker_factor
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (kappa : K) (functional : Encoded)
    (functionalRun : fromInputs out gamma kappa body z = some functional)
    (digest : Block) :
    compileScript
        (bind (m := 1)
          (afterFunctionalBeforeMarkerScript out gamma body z kappa functional
            functionalRun digest) fun boundaryDraw =>
          match boundaryDraw.1 with
          | .error e => .done (Except.error e, boundaryDraw.2)
          | .ok boundary => alphaMarkerContinuation out gamma body z boundary) =
      compileScript
        (afterFunctionalPreAlphaScript out gamma body z kappa functional
          functionalRun digest) := by
  unfold afterFunctionalBeforeMarkerScript afterFunctionalPreAlphaScript
    alphaMarkerContinuation
  simp only [compileScript_bind, bindOracleMachine_assoc]
  apply congrArg (bindOracleMachine
    (compileScript (absorbScript digest 1 functional.description)))
  funext afterDescription
  apply congrArg (bindOracleMachine
    (compileScript (absorbScript afterDescription 6 functional.claim)))
  funext afterClaim
  apply congrArg (bindOracleMachine
    (compileScript (absorbScript afterClaim 1 compactFunctionalProfile)))
  funext afterImageProfile
  apply congrArg (bindOracleMachine
    (compileScript (nonzeroScript 3 afterImageProfile)))
  funext tauDraw
  cases tauDraw.1 with
  | error e => rfl
  | ok tau =>
      simp only [compileScript_bind, bindOracleMachine_assoc]
      apply congrArg (bindOracleMachine
        (compileScript (absorbScript tauDraw.2 52
          (0 :: response0Bytes body))))
      funext afterResponse0
      rfl

private theorem compile_afterKappa_before_marker_factor
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (kappa : K) (digest : Block) :
    compileScript
        (bind (m := 1)
          (match functionalRun : fromInputs out gamma kappa body z with
          | none => .done
              (Except.error FSLiveSourceFunctionalMiddle.Error.functional,
                digest)
          | some functional =>
              afterFunctionalBeforeMarkerScript out gamma body z kappa
                functional functionalRun digest) fun boundaryDraw =>
          match boundaryDraw.1 with
          | .error e => .done (Except.error e, boundaryDraw.2)
          | .ok boundary => alphaMarkerContinuation out gamma body z boundary) =
      compileScript
        (match functionalRun : fromInputs out gamma kappa body z with
        | none => .done
            (Except.error FSLiveSourceFunctionalMiddle.Error.functional,
              digest)
        | some functional =>
            afterFunctionalPreAlphaScript out gamma body z kappa functional
              functionalRun digest) := by
  split
  · simp only [compileScript_bind, compileScript, bindOracleMachine]
  · rename_i functional functionalRun
    exact compile_afterFunctional_before_marker_factor out gamma body z kappa
      functional functionalRun digest

/-- The same factorization also preserves the compiled V7 oracle machine
syntax; no pointwise interpreter extensionality is used here. -/
theorem compile_factoredPreAlphaScript_eq_preAlphaScript
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) :
    compileScript (factoredPreAlphaScript out gamma body z digest) =
      compileScript (preAlphaScript out gamma body z digest) := by
  unfold factoredPreAlphaScript beforeAlphaMarkerScript preAlphaScript
  simp only [compileScript_bind, bindOracleMachine_assoc]
  apply congrArg (bindOracleMachine
    (compileScript (absorbScript digest 50 (inactiveClaimBytes body))))
  funext afterInactive
  apply congrArg (bindOracleMachine
    (compileScript (nonzeroScript 3 afterInactive)))
  funext kappaDraw
  cases kappaDraw.1 with
  | error e => rfl
  | ok kappa =>
      rw [← compileScript_bind]
      exact compile_afterKappa_before_marker_factor out gamma body z kappa
        kappaDraw.2

#print axioms run_factoredPreAlphaScript_eq_preAlphaScript
#print axioms compile_factoredPreAlphaScript_eq_preAlphaScript
#print axioms successful_beforeAlphaMarker_digest
#print axioms run_alphaMarkerContinuation

end
end AspisV8Completion.FSV8BeforeAlphaMarkerFactorization
