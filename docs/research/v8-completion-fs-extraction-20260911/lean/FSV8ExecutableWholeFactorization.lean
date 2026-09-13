import FSV8ExecutablePreAlphaFactorization
import FSAuthenticatedInterleavedPrefixMiddle

/-!
# Whole selected verifier factorization at the ordinary-alpha boundary

`FSV8ExecutablePreAlphaFactorization` proves that the source-shaped middle can
be stopped immediately before the ordinary alpha sampler and resumed without
changing either its result or oracle state.  This leaf lifts that equality
through the already-selected source/OOD/gamma prefix and authenticated suffix.

The theorem is pointwise for every body, tape, entry oracle, and work script.
It introduces no successful-run or freshness premise.  Consequently the
factored script can replace `wholeStagedScript` in a forward scheduler without
changing the functional verifier execution.  It does not yet prove the
cache-aware probability law for the one-to-four alpha squeeze pairs.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2400

namespace AspisV8Completion.FSV8ExecutableWholeFactorization

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript
open FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8ExecutablePreAlphaFactorization

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

theorem middleBudget_eq_factoredBudget :
    middleBudget = postAlphaBudget + preAlphaBudget := by
  decide

/-- The selected middle wrapper with the executable pre-alpha cut exposed. -/
def factoredMiddleContinuationAt (body : Bytes) (z : Fin 10 → K)
    (out : OODResult) (gamma : K) (digest : Block) :
    Script Bytes Block (Except FSAuthenticatedInterleavedPrefixMiddle.Error
      (Partial body z) × Block) middleBudget := by
  exact bind (m := 0) (factoredMiddleScript out gamma body z digest)
    fun middleDraw =>
      .done (match middleDraw.1 with
        | .error e => (.error (.middle e), middleDraw.2)
        | .ok middle =>
            (.ok { out := out, gamma := gamma, middle := middle }, middleDraw.2))

/-- The actual source/OOD/gamma prefix followed by the factored middle. -/
def factoredPrefixMiddleScript {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block) :
    Script Bytes Block (Except FSAuthenticatedInterleavedPrefixMiddle.Error
      (Partial body z) × Block)
      (middleBudget + (1 + 3*66 + (1+m+594+1+n+198))) :=
  bind (m := middleBudget)
    (sourceThenGammaScript firstWork secondWork body digest) fun prefixDraw =>
      match prefixDraw.1 with
      | .error e => .done (.error (.prefix e), prefixDraw.2)
      | .ok (out, gamma) =>
          factoredMiddleContinuationAt body z out gamma prefixDraw.2

/-- Complete selected functional verifier with the pre-alpha cut exposed. -/
def factoredWholeStagedScript {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (body : Bytes) (digest : Block) :
    Script Bytes Block (Except FSAuthenticatedInterleavedPrefixMiddle.Error
      (Record body z) × Block)
      (1038 + (middleBudget + (1 + 3*66 + (1+m+594+1+n+198)))) :=
  bind (m := 1038)
    (factoredPrefixMiddleScript firstWork secondWork z body digest) fun p =>
      match p.1 with
      | .error e => .done (.error e, p.2)
      | .ok staged => suffixContinuation cuts body z p.2 staged

theorem run_factoredMiddleContinuationAt_eq_middleContinuationAt
    (body : Bytes) (z : Fin 10 → K) (out : OODResult) (gamma : K)
    (digest : Block) (tape : Tape) (oracle : Oracle) :
    run tape (factoredMiddleContinuationAt body z out gamma digest) oracle =
      run tape (middleContinuationAt body z out gamma digest) oracle := by
  unfold factoredMiddleContinuationAt middleContinuationAt
  rw [FSTranscriptScript.run_bind, FSTranscriptScript.run_bind]
  rw [run_factoredMiddleScript_eq_middleScript]
  rfl

theorem run_factoredPrefixMiddleScript_eq_prefixMiddleScript {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : Oracle) :
    run tape (factoredPrefixMiddleScript firstWork secondWork z body digest)
        oracle =
      run tape (prefixMiddleScript firstWork secondWork z body digest) oracle := by
  unfold factoredPrefixMiddleScript prefixMiddleScript
  rw [FSTranscriptScript.run_bind, FSTranscriptScript.run_bind]
  cases prefixRun :
      run tape (sourceThenGammaScript firstWork secondWork body digest) oracle with
  | mk result prefixOracle =>
      cases result with
      | none => simp
      | some value =>
          rcases value with ⟨prefixResult, prefixDigest⟩
          cases prefixResult with
          | error e => simp [run]
          | ok pair =>
              rcases pair with ⟨out, gamma⟩
              exact run_factoredMiddleContinuationAt_eq_middleContinuationAt
                body z out gamma prefixDigest tape prefixOracle

/-- Full result-and-oracle equality for the same body.  This is the exact
functional replacement theorem needed by the forward scheduler root. -/
theorem run_factoredWholeStagedScript_eq_wholeStagedScript {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : Oracle) :
    run tape
        (factoredWholeStagedScript firstWork secondWork z cuts body digest)
        oracle =
      run tape (wholeStagedScript firstWork secondWork z cuts body digest)
        oracle := by
  unfold factoredWholeStagedScript wholeStagedScript
  rw [FSTranscriptScript.run_bind, FSTranscriptScript.run_bind]
  rw [run_factoredPrefixMiddleScript_eq_prefixMiddleScript]
  rfl

#print axioms middleBudget_eq_factoredBudget
#print axioms factoredMiddleContinuationAt
#print axioms factoredPrefixMiddleScript
#print axioms factoredWholeStagedScript
#print axioms run_factoredMiddleContinuationAt_eq_middleContinuationAt
#print axioms run_factoredPrefixMiddleScript_eq_prefixMiddleScript
#print axioms run_factoredWholeStagedScript_eq_wholeStagedScript

end
end AspisV8Completion.FSV8ExecutableWholeFactorization
