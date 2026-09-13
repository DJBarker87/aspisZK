import FSV8ExactRootCursor
import FSV8ExecutablePreAlphaFactorization
import AspisFormal.K1.V7Tag73SchedulerNativeForkPairReplay

/-!
# Forward V8 verifier boundary to the first ordinary-alpha fork pair

This leaf runs the source/OOD/gamma prefix and the executable pre-alpha
factorization before emitting the first ordinary alpha output/advance pair.
The returned value retains the dependent `PreAlpha` boundary produced by the
same verifier execution.  It does not reconstruct that boundary backwards.

This is deliberately only the first-pair operational bridge.  An ordinary
alpha can consume one to four answer-dependent pairs.  The existing V7 K15
router supplies the complete eight-coordinate probability decomposition, but
does not itself program the used pairs or prove cache-aware source coupling.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 2000

namespace AspisV8Completion.FSV8ForwardAlphaForkCursor

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeForkPairReplay
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73OperationalCausalInjection
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript
open FSV8ActualAlphaAtomicPairInputs
open FSV8ExactRootCursor
open FSV8ExecutablePreAlphaFactorization
open FSV8V7OracleMachineBridge

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

inductive BoundaryError where
  | prefix (error : Sum FSOODSampler.Error FSNonzeroQM31.Error)
  | middle (error : FSLiveSourceFunctionalMiddle.Error)
  | noPairRoom
  deriving DecidableEq

/-- The dependent boundary is an output of the executed verifier prefix. -/
structure ExecutedPreAlpha (body : Bytes) (z : Fin 10 → K) where
  out : OODResult
  gamma : K
  boundary : PreAlpha out gamma body z

def verifierPreAlphaScript {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block) :
    Script Bytes Block
      (Except BoundaryError (ExecutedPreAlpha body z) × Block)
      (preAlphaBudget + ((1 + 3*66) + (((1+m)+594+1+n)+198))) :=
  FSTranscriptScript.bind (m := preAlphaBudget)
      (sourceThenGammaScript firstWork secondWork body digest) fun prefixDraw =>
    match prefixDraw.1 with
    | .error error => .done
        (Except.error (BoundaryError.prefix error), prefixDraw.2)
    | .ok (out, gamma) =>
      FSTranscriptScript.bind (m := 0)
          (preAlphaScript out gamma body z prefixDraw.2)
        fun boundaryDraw =>
          match boundaryDraw.1 with
          | .error error => .done
              (Except.error (BoundaryError.middle error), boundaryDraw.2)
          | .ok boundary => .done
              (Except.ok (ExecutedPreAlpha.mk out gamma boundary),
                boundaryDraw.2)

structure ForkedBoundary (z : Fin 10 → K) where
  body : Bytes
  executed : ExecutedPreAlpha body z
  beforeAlpha : FSBoundedTranscript.Transcript
  digest_eq : beforeAlpha.digest = executed.boundary.digest
  scheduled : AtomicPairReplayConfiguration

/-- Forward root through the actual executable pre-alpha boundary, then emit
the first ordinary-alpha pair.  Boundary rejection and insufficient pair
room remain typed results rather than invented scheduler failures. -/
def rootToAlphaForkCursor
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (template : AtomicPairReplayConfiguration) (hidden : HiddenTape) :
    SchedulerNativeCursor globalOracleCalls
      (Except BoundaryError (ForkedBoundary configuration.z)) :=
  .machine configuration.adversaryLimits
    configuration.adversaryLimitBound .adversary emptyOracle
    (configuration.blackBox.start hidden configuration.observation)
    configuration.adversaryFuel empty_oracle_history_total_coherent
    (fun body proverFinalOracle proverCoherent =>
      .machine configuration.verifierLimits
        configuration.verifierLimitBound .verifier proverFinalOracle
        (compileScript (verifierPreAlphaScript configuration.firstWork
          configuration.secondWork configuration.z body
          configuration.initialDigest))
        (preAlphaBudget + ((1 + 3*66) + (((1+m)+594+1+n)+198)))
        proverCoherent
        (fun output verifierBoundaryOracle _ =>
          match output.1 with
          | .error error => .returned (Except.error error)
          | .ok executed =>
            let beforeAlpha : FSBoundedTranscript.Transcript :=
              { digest := executed.boundary.digest
                oracle := projectOracleState verifierBoundaryOracle }
            if pairRoom : verifierBoundaryOracle.history.length + 2 ≤
                globalOracleCalls then
              .forkPair verifierBoundaryOracle.history pairRoom
                (alphaAtomicPairInputs beforeAlpha).1
                (alphaAtomicPairInputs beforeAlpha).2 template
                (fun scheduled => .returned (Except.ok
                  { body := body
                    executed := executed
                    beforeAlpha := beforeAlpha
                    digest_eq := rfl
                    scheduled := scheduled }))
            else .returned (Except.error BoundaryError.noPairRoom)))

/-- Supplying the first two scheduler coordinates reaches the continuation
with those exact coordinates.  This theorem does not claim that alpha has
decoded or that the remaining three pairs are unnecessary. -/
theorem emitted_alpha_fork_pair_exact
    {globalOracleCalls : Nat} (z : Fin 10 → K)
    (transitionFuel : Nat) (body : Bytes)
    (executed : ExecutedPreAlpha body z)
    (beforeAlpha : FSBoundedTranscript.Transcript)
    (digestEq : beforeAlpha.digest = executed.boundary.digest)
    (history : List QueryRecord)
    (pairRoom : history.length + 2 ≤ globalOracleCalls)
    (template : AtomicPairReplayConfiguration)
    (forkOutput forkAdvance : Block) :
    let next := fun scheduled =>
      (.returned (Except.ok
        { body := body
          executed := executed
          beforeAlpha := beforeAlpha
          digest_eq := digestEq
          scheduled := scheduled }) :
        SchedulerNativeCursor globalOracleCalls
          (Except BoundaryError (ForkedBoundary z)))
    schedulerNativePrefixCursor (transitionFuel + 1)
      (.forkPair history pairRoom
        (alphaAtomicPairInputs beforeAlpha).1
        (alphaAtomicPairInputs beforeAlpha).2 template next)
      [forkOutput, forkAdvance] =
        next (scheduledForkConfiguration template forkOutput forkAdvance) := by
  exact scheduler_native_prefix_cursor_fork_pair_exact transitionFuel history
    pairRoom (alphaAtomicPairInputs beforeAlpha).1
    (alphaAtomicPairInputs beforeAlpha).2 template _ forkOutput forkAdvance

#print axioms verifierPreAlphaScript
#print axioms rootToAlphaForkCursor
#print axioms emitted_alpha_fork_pair_exact

end
end AspisV8Completion.FSV8ForwardAlphaForkCursor
