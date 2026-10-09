import FSLiveSourceFunctionalMiddle
import FSV8ActualAlphaAtomicPairInputs

/-!
# Executable pre-alpha factorization

This leaf factors the selected source-functional middle at its real alpha0
boundary.  `preAlphaScript` executes every operation through absorption of the
alpha nonce, then returns.  A scheduler callback therefore receives both the
returned prefix value and the exact `OracleState` at which the ordinary
`candidateScript` begins.

The continuation retains the complete cache-aware alpha candidate sampler:
alpha0 is not a nonzero sampler, zero is legal, and limb sentinels can cause
one to four squeeze pairs before its bounded limb decoder terminates.  The
first pair theorem only identifies the adjacent first output/advance pair; it
does not claim that pair completes alpha sampling.

The final theorem proves equality of the complete result and oracle state of
the factored middle and the existing `middleScript`, for every tape and entry
oracle.  Thus the factorization preserves the full query trace rather than
assuming a log correspondence.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000

namespace AspisV8Completion.FSV8ExecutablePreAlphaFactorization

open AspisK1.V7FsAokExperiment
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31
open FSV7OODSampler
open FSLiveQueryRhoSuffix FSLiveSelectedMiddleQueryRho
open SameBodyFunctionalProducerSource
open FSLiveSourceFunctionalMiddle
open FSV8V7OracleMachineBridge
open FSV8ActualAlphaAtomicPairInputs

noncomputable section

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

abbrev preAlphaBudget : Nat := 402
abbrev postAlphaBudget : Nat := 283

/-- Values fixed at the exact prefix cut.  The live oracle state is returned
by `run`/the SchedulerNative machine callback, not copied into this value. -/
structure PreAlpha (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) where
  kappa : K
  tau : K
  functional : Encoded
  functionalRun : fromInputs out gamma kappa body z = some functional
  digest : Block

/-- Execute the portion after successful functional construction up to, but
not including, the first alpha candidate request. -/
def afterFunctionalPreAlphaScript (out : OODResult) (gamma : K)
    (body : Bytes) (z : Fin 10 → K) (kappa : K)
    (functional : Encoded)
    (functionalRun : fromInputs out gamma kappa body z = some functional)
    (digest : Block) :
    Script Bytes Block
      (Except FSLiveSourceFunctionalMiddle.Error
        (PreAlpha out gamma body z) × Block) 203 :=
  bind (m := 202) (absorbScript digest 1 functional.description)
      fun afterDescription =>
    bind (m := 201) (absorbScript afterDescription 6 functional.claim)
        fun afterClaim =>
      bind (m := 200) (absorbScript afterClaim 1 compactFunctionalProfile)
          fun afterImageProfile =>
        bind (m := 2) (nonzeroScript 3 afterImageProfile) fun tauDraw =>
          match tauDraw.1 with
          | .error e => .done
              (Except.error (FSLiveSourceFunctionalMiddle.Error.tau e),
                tauDraw.2)
          | .ok tau =>
            bind (m := 1)
                (absorbScript tauDraw.2 52 (0 :: response0Bytes body))
                fun afterResponse0 =>
              bind (m := 0) (absorbScript afterResponse0 20
                  (0 :: alpha0NonceBytes body)) fun afterAlphaNonce =>
                .done
                  (Except.ok
                    { kappa := kappa
                      tau := tau
                      functional := functional
                      functionalRun := functionalRun
                      digest := afterAlphaNonce },
                    afterAlphaNonce)

/-- Executable prefix from the actual middle entry through the alpha nonce. -/
def preAlphaScript (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (digest : Block) :
    Script Bytes Block
      (Except FSLiveSourceFunctionalMiddle.Error
        (PreAlpha out gamma body z) × Block) preAlphaBudget :=
  bind (m := 401) (absorbScript digest 50 (inactiveClaimBytes body))
      fun afterInactive =>
    bind (m := 203) (nonzeroScript 3 afterInactive) fun kappaDraw =>
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
          afterFunctionalPreAlphaScript out gamma body z kappa functional
            functionalRun kappaDraw.2

/-- The unchanged ordinary alpha candidate and query/rho continuation. -/
def postAlphaScript (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (boundary : PreAlpha out gamma body z) :
    Script Bytes Block (FSLiveSourceFunctionalMiddle.Result out gamma body z ×
      Block) postAlphaBudget :=
  bind (m := 217) (candidateScript boundary.digest) fun alphaDraw =>
    match alphaDraw.1 with
    | .error e => .done
        (Except.error (FSLiveSourceFunctionalMiddle.Error.alpha0 e),
          alphaDraw.2)
    | .ok alpha0 =>
      bind (m := 0) (queryRhoScript body alphaDraw.2) fun suffixDraw =>
        .done (match suffixDraw.1 with
          | .error e =>
            (Except.error (FSLiveSourceFunctionalMiddle.Error.suffix e),
              suffixDraw.2)
          | .ok (queries, rho) =>
            let middle := FSLiveSelectedMiddleQueryRho.Success.mk
              boundary.kappa boundary.tau alpha0 queries rho
            let sourceSuccess :
                FSLiveSourceFunctionalMiddle.Success out gamma body z :=
              { middle := middle
                functional := boundary.functional
                functionalRun := boundary.functionalRun }
            (Except.ok sourceSuccess, suffixDraw.2))

/-- The forward split used by a scheduler: the callback occurs at the exact
pre-alpha oracle state and resumes with the ordinary candidate sampler. -/
def factoredMiddleScript (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (digest : Block) :
    Script Bytes Block (FSLiveSourceFunctionalMiddle.Result out gamma body z ×
      Block) (postAlphaBudget + preAlphaBudget) :=
  bind (m := postAlphaBudget) (preAlphaScript out gamma body z digest)
    fun prefixDraw =>
      match prefixDraw.1 with
      | .error e => .done (Except.error e, prefixDraw.2)
      | .ok boundary => postAlphaScript out gamma body z boundary

theorem postAlphaScript_starts_with_complete_candidate
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (boundary : PreAlpha out gamma body z) :
    ∃ next : Block → Block →
        OracleMachine (Except FSNonzeroQM31.Error K × Block),
      compileScript (candidateScript boundary.digest) =
        .query (alphaAtomicPairInputs ⟨boundary.digest,
          (FSFirstFresh.empty : Oracle)⟩).1 (fun output =>
          .query (alphaAtomicPairInputs ⟨boundary.digest,
            (FSFirstFresh.empty : Oracle)⟩).2 (next output)) := by
  exact compiled_alpha_candidate_starts_with_atomic_pair
    ⟨boundary.digest, (FSFirstFresh.empty : Oracle)⟩

private theorem run_afterFunctional_factor
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (kappa : K) (functional : Encoded)
    (functionalRun : fromInputs out gamma kappa body z = some functional)
    (digest : Block) (tape : Tape) (oracle : Oracle) :
    run tape
        (bind (m := postAlphaBudget)
          (afterFunctionalPreAlphaScript out gamma body z kappa functional
            functionalRun digest) fun boundaryDraw =>
          match boundaryDraw.1 with
          | .error e => .done (Except.error e, boundaryDraw.2)
          | .ok boundary => postAlphaScript out gamma body z boundary)
        oracle =
      run tape
        (afterFunctionalScript out gamma body z kappa functional
          functionalRun digest) oracle := by
  let s0 : FSBoundedTranscript.Transcript := ⟨digest, oracle⟩
  let s1 := FSBoundedTranscript.absorb tape s0 1 functional.description
  have h1 : run tape (absorbScript digest 1 functional.description) oracle =
      (some s1.digest, s1.oracle) := by
    exact FSTranscriptScript.run_absorb tape s0 1 functional.description
  unfold afterFunctionalPreAlphaScript afterFunctionalScript postAlphaScript
  rw [FSTranscriptScript.run_bind]
  simp only [FSTranscriptScript.run_bind, h1, Prod.fst, Prod.snd]
  let s2 := FSBoundedTranscript.absorb tape s1 6 functional.claim
  have h2 : run tape (absorbScript s1.digest 6 functional.claim) s1.oracle =
      (some s2.digest, s2.oracle) := FSTranscriptScript.run_absorb _ _ _ _
  simp only [h2, Prod.fst, Prod.snd]
  let s3 := FSBoundedTranscript.absorb tape s2 1 compactFunctionalProfile
  have h3 : run tape (absorbScript s2.digest 1 compactFunctionalProfile) s2.oracle =
      (some s3.digest, s3.oracle) := FSTranscriptScript.run_absorb _ _ _ _
  simp only [h3, Prod.fst, Prod.snd]
  have ht := FSNonzeroQM31.run_nonzero tape 3 s3
  simp only [ht, Prod.fst, Prod.snd]
  cases tauResult : (FSNonzeroQM31.nonzero tape 3 s3).1 with
  | error e => simp [tauResult, run]
  | ok tau =>
    simp only [tauResult]
    let s4 := FSBoundedTranscript.absorb tape
      (FSNonzeroQM31.nonzero tape 3 s3).2 52 (0 :: response0Bytes body)
    have h4 : run tape
        (absorbScript (FSNonzeroQM31.nonzero tape 3 s3).2.digest 52
          (0 :: response0Bytes body))
        (FSNonzeroQM31.nonzero tape 3 s3).2.oracle =
        (some s4.digest, s4.oracle) := FSTranscriptScript.run_absorb _ _ _ _
    rw [FSTranscriptScript.run_bind, h4]
    simp only [Prod.fst, Prod.snd]
    let s5 := FSBoundedTranscript.absorb tape s4 20
      (0 :: alpha0NonceBytes body)
    have h5 : run tape (absorbScript s4.digest 20
        (0 :: alpha0NonceBytes body)) s4.oracle =
        (some s5.digest, s5.oracle) := FSTranscriptScript.run_absorb _ _ _ _
    rw [FSTranscriptScript.run_bind, h5]
    simp only [Prod.fst, Prod.snd, run]
    conv_rhs =>
      rw [FSTranscriptScript.run_bind, h4]
      simp only [Prod.fst, Prod.snd]
      rw [FSTranscriptScript.run_bind, h5]
      simp only [Prod.fst, Prod.snd]
    congr

private theorem run_afterKappa_factor
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (kappa : K) (digest : Block) (tape : Tape) (oracle : Oracle) :
    run tape
        (bind (m := postAlphaBudget)
          (match functionalRun : fromInputs out gamma kappa body z with
          | none => .done
              (Except.error FSLiveSourceFunctionalMiddle.Error.functional,
                digest)
          | some functional =>
              afterFunctionalPreAlphaScript out gamma body z kappa functional
                functionalRun digest) fun boundaryDraw =>
          match boundaryDraw.1 with
          | .error e => .done (Except.error e, boundaryDraw.2)
          | .ok boundary => postAlphaScript out gamma body z boundary)
        oracle =
      run tape
        (match functionalRun : fromInputs out gamma kappa body z with
        | none => .done
            (Except.error FSLiveSourceFunctionalMiddle.Error.functional,
              digest)
        | some functional =>
            afterFunctionalScript out gamma body z kappa functional
              functionalRun digest)
        oracle := by
  split
  · simp [FSTranscriptScript.run_bind, run]
  · rename_i functional functionalRun
    exact run_afterFunctional_factor out gamma body z kappa functional
      functionalRun digest tape oracle

/-- Runtime equivalence is the interface needed before replacing the old
middle by the forward split inside the unified scheduler root. -/
theorem run_factoredMiddleScript_eq_middleScript
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (tape : Tape) (oracle : Oracle) :
    run tape (factoredMiddleScript out gamma body z digest) oracle =
      run tape (middleScript out gamma body z digest) oracle := by
  let s0 : FSBoundedTranscript.Transcript := ⟨digest, oracle⟩
  let s1 := FSBoundedTranscript.absorb tape s0 50 (inactiveClaimBytes body)
  have h1 : run tape (absorbScript digest 50 (inactiveClaimBytes body)) oracle =
      (some s1.digest, s1.oracle) := by
    exact FSTranscriptScript.run_absorb tape s0 50 (inactiveClaimBytes body)
  unfold factoredMiddleScript preAlphaScript middleScript
  rw [FSTranscriptScript.run_bind]
  simp only [FSTranscriptScript.run_bind, h1, Prod.fst, Prod.snd]
  have hk := FSNonzeroQM31.run_nonzero tape 3 s1
  simp only [hk, Prod.fst, Prod.snd]
  cases kappaResult : (FSNonzeroQM31.nonzero tape 3 s1).1 with
  | error e => simp [kappaResult, run]
  | ok kappa =>
    simp only [kappaResult]
    rw [← FSTranscriptScript.run_bind]
    exact run_afterKappa_factor out gamma body z kappa
      (FSNonzeroQM31.nonzero tape 3 s1).2.digest tape
      (FSNonzeroQM31.nonzero tape 3 s1).2.oracle

#print axioms preAlphaScript
#print axioms postAlphaScript
#print axioms factoredMiddleScript
#print axioms postAlphaScript_starts_with_complete_candidate
#print axioms run_afterFunctional_factor
#print axioms run_afterKappa_factor
#print axioms run_factoredMiddleScript_eq_middleScript

end
end AspisV8Completion.FSV8ExecutablePreAlphaFactorization
