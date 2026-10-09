import FSV8AlphaTableHistoryCoverage
import FSV8V7HistoryProjectionAlignment

/-!
# Fresh-only provenance at the live alpha entry

The general programmed cut cannot imply `NoProgrammed`: its initial table may
contain restoration entries.  The actual forward projected root is narrower.
It starts at `emptyOracle`, and the adversary, source/gamma, and pre-alpha
segments all use `runMachine`, which only performs ordinary oracle queries.
This leaf constructs the fresh-only prerequisite for that source branch.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000

namespace AspisV8Completion.FSV8ProjectedRootPreAlphaNoProgrammed

open FSBoundedTranscript
open FSV8PostOODGammaScript FSV8V7OracleMachineBridge
open FSV8ExecutablePreAlphaFactorization
open FSV8V7StateAlignment FSV8V7HistoryProjectionAlignment
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- A returned projected adversary run from the literal empty oracle contains
no programmed table entry. -/
theorem projected_adversary_root_no_programmed
    {Result : Type*} (limits : OracleLimits) (fuel : Nat)
    (program : OracleMachine Result) (available : List Digest256)
    (returned : ProjectedMachinePrefixReturned limits .adversary fuel
      emptyOracle program available) :
    NoProgrammed returned.finalState := by
  let controller := controllerFromProjectedFreshAnswers emptyOracle.history
    (returned.freshQueries.map Prod.snd)
  have exactRun := projected_machine_prefix_returned_run_exact limits
    .adversary fuel emptyOracle program available returned
      empty_oracle_history_total_coherent
  have preserved := run_machine_preserves_no_programmed controller limits
    .adversary fuel emptyOracle program (by simp [NoProgrammed, emptyOracle])
  simpa [controller, exactRun] using preserved

/-- The exact source/gamma and pre-alpha segments preserve fresh-only table
provenance from the same projected root.  No cut-success or target premise is
needed; the result holds for every halt disposition of these query-only runs. -/
theorem projected_root_constructs_preAlpha_no_programmed
    {Result : Type*} {steps : Nat} {tape : Tape}
    (finiteTape : FreshAnswerTape Block steps)
    (rootLimits : OracleLimits) (rootFuel : Nat)
    (verifierLimits : OracleLimits) (verifierFuel : Nat)
    (rootProgram : OracleMachine Result) (available : List Digest256)
    (root : ProjectedMachinePrefixReturned rootLimits .adversary rootFuel
      emptyOracle rootProgram available)
    {n m : Nat}
    (firstWork : Point → FSOracleExecution.Script (List UInt8) Block Unit n)
    (secondWork : Point → Point →
      FSOracleExecution.Script (List UInt8) Block Unit m)
    (body : List UInt8) (digest : Block)
    (out : FSV8PostOODGammaScript.OODResult) (gamma : K)
    (z : Fin 10 → K) (sourceDigest : Block) :
    let sourceRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      verifierLimits .verifier verifierFuel root.finalState
      (compileScript
        (sourceThenGammaScript firstWork secondWork body digest))
    let preRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      verifierLimits .verifier (verifierFuel - sourceRun.steps) sourceRun.oracle
      (compileScript (preAlphaScript out gamma body z sourceDigest))
    NoProgrammed sourceRun.oracle ∧ NoProgrammed preRun.oracle := by
  dsimp only
  have rootFresh := projected_adversary_root_no_programmed rootLimits rootFuel
    rootProgram available root
  have sourceFresh := run_machine_preserves_no_programmed
    (controllerFromFreshAnswerTape finiteTape) verifierLimits .verifier
    verifierFuel root.finalState
    (compileScript (sourceThenGammaScript firstWork secondWork body digest))
    rootFresh
  have preFresh := run_machine_preserves_no_programmed
    (controllerFromFreshAnswerTape finiteTape) verifierLimits .verifier
    (verifierFuel -
      (runMachine (controllerFromFreshAnswerTape finiteTape) verifierLimits
        .verifier verifierFuel root.finalState
        (compileScript
          (sourceThenGammaScript firstWork secondWork body digest))).steps)
    (runMachine (controllerFromFreshAnswerTape finiteTape) verifierLimits
      .verifier verifierFuel root.finalState
      (compileScript
        (sourceThenGammaScript firstWork secondWork body digest))).oracle
    (compileScript (preAlphaScript out gamma body z sourceDigest)) sourceFresh
  exact ⟨sourceFresh, preFresh⟩

#print axioms projected_adversary_root_no_programmed
#print axioms projected_root_constructs_preAlpha_no_programmed

end
end AspisV8Completion.FSV8ProjectedRootPreAlphaNoProgrammed
