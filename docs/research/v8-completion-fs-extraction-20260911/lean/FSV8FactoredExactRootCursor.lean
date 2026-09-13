import FSV8ExactRootCursor
import FSV8CompiledWholeFactorization

/-!
# The exact forward root with the executable pre-alpha factorization

This leaf substitutes the factored compiled verifier into the exact same-body
root cursor and proves that the resulting scheduler cursor is literally equal
to the existing root.  The adversary, returned body, initial oracle, limits,
actor, fuel, callbacks and dependent result are unchanged.

This is not the later split-callback construction: `compileScript` still
contains the internal bind.  It establishes that exposing that bind starts
from the exact probability-visible root rather than a second verifier model.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8FactoredExactRootCursor

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73OperationalCausalInjection
open FSBoundedTranscript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8ExactRootCursor
open FSV8ExecutableWholeFactorization
open FSV8CompiledWholeFactorization

noncomputable section

/-- Same exact root, with only the structurally equal compiled verifier
program spelling changed. -/
def factoredRootCursor
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape) :
    SchedulerNativeCursor globalOracleCalls
      (Runtime TapeIdentity configuration.z) :=
  .machine configuration.adversaryLimits
    configuration.adversaryLimitBound .adversary emptyOracle
    (configuration.blackBox.start hidden configuration.observation)
    configuration.adversaryFuel empty_oracle_history_total_coherent
    (fun body proverFinalOracle proverCoherent =>
      .machine configuration.verifierLimits
        configuration.verifierLimitBound .verifier proverFinalOracle
        (compileScript (factoredWholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts body
          configuration.initialDigest))
        (stagedBudget n m) proverCoherent
        (fun output verifierFinalOracle _ =>
          .returned
            { tapeIdentity := configuration.tapeIdentity hidden
              body := body
              proverFinalOracle := proverFinalOracle
              verifierFinalOracle := verifierFinalOracle
              output := output }))

/-- Literal scheduler-cursor equality.  It preserves normalization and every
exposure trace by rewriting, without a run-success or freshness premise. -/
theorem factoredRootCursor_eq_rootCursor
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape) :
    factoredRootCursor configuration hidden = rootCursor configuration hidden := by
  simp only [factoredRootCursor, rootCursor,
    compile_factoredWholeStagedScript_eq_wholeStagedScript]

/-- The probability-visible exposure source is also the erasure of the
factored exact root. -/
theorem factored_root_erasure_is_exact_exposure
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape) :
    (factoredRootCursor configuration hidden).erase =
      exposureCursor configuration hidden := by
  rw [factoredRootCursor_eq_rootCursor]
  rfl

#print axioms factoredRootCursor
#print axioms factoredRootCursor_eq_rootCursor
#print axioms factored_root_erasure_is_exact_exposure

end
end AspisV8Completion.FSV8FactoredExactRootCursor
