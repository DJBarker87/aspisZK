import FSV8ProgrammedProjectionAlignment
import AspisFormal.K1.V7Tag73ProjectedMachinePrefix

/-!
# Actual-tape projection facts for one returned scheduler machine prefix

A returned projected machine prefix starting at `emptyOracle` consumes a
literal prefix of the supplied finite answer tape.  This leaf packages the
resulting final oracle against that same tape; it does not replace the tape by
a history-derived or padded analysis tape.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.FSV8ProjectedPrefixProjectionFacts

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open FSBoundedTranscript
open FSV8V7WholeScriptUniformLaw
open FSV8ProgrammedProjectionAlignment

noncomputable section

universe u

abbrev Block := FSBoundedTranscript.Block

/-- The final state of an actually returned machine prefix from the empty
oracle is aligned with the literal finite tape supplied to that prefix.
`fallback` only totalizes the tape beyond its finite support; compatibility on
the finite support is proved below. -/
theorem returned_from_empty_projectionFacts
    {Result : Type u} {steps : Nat}
    (finiteTape : FreshAnswerTape Block steps) (fallback : Block)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (program : OracleMachine Result)
    (returned : ProjectedMachinePrefixReturned limits actor fuel emptyOracle
      program (freshAnswerTapeToList finiteTape)) :
    ProjectionFacts (extendFreshTape finiteTape fallback) finiteTape
      returned.finalState := by
  have answersSince :=
    projected_machine_prefix_fresh_answers_are_history_suffix limits actor fuel
      emptyOracle program (freshAnswerTapeToList finiteTape) returned
  have answersExact :
      freshAnswerEnumeration returned.finalState.history =
        returned.freshQueries.map Prod.snd := by
    simpa [historySince, emptyOracle] using answersSince
  have freshCallsExact := projected_fresh_returned_trace_fresh_calls_exact
    limits actor fuel emptyOracle program returned.freshQueries returned.result
    returned.finalState returned.steps returned.trace
  have freshCount : FreshHistoryCountCoherent returned.finalState := by
    unfold FreshHistoryCountCoherent
    rw [answersExact, List.length_map, freshCallsExact]
    simp [emptyOracle]
  have consumedLe : returned.freshQueries.length ≤ steps := by
    have lengths := congrArg List.length returned.availableExact
    simp only [List.length_append, List.length_map,
      fresh_answer_tape_to_list_length] at lengths
    omega
  have within : WithinFreshAnswerTape finiteTape returned.finalState := by
    refine ⟨freshCount, ?_⟩
    rw [freshCallsExact]
    simpa [emptyOracle] using consumedLe
  have tapeMatches : FreshHistoryMatchesTape finiteTape returned.finalState := by
    unfold FreshHistoryMatchesTape
    rw [answersExact, freshCallsExact]
    simp only [emptyOracle, Nat.zero_add]
    calc
      returned.freshQueries.map Prod.snd =
          (returned.freshQueries.map Prod.snd ++ returned.remaining).take
            returned.freshQueries.length := by simp
      _ = (freshAnswerTapeToList finiteTape).take
            returned.freshQueries.length := by
          exact congrArg (List.take returned.freshQueries.length)
            returned.availableExact.symm
  exact
    { historyTotal := returned.finalCoherent
      freshCount := freshCount
      tapeMatches := tapeMatches
      withinTape := within
      tapeCompatibility := extendFreshTape_compatible finiteTape fallback }

#print axioms returned_from_empty_projectionFacts

end
end AspisV8Completion.FSV8ProjectedPrefixProjectionFacts
