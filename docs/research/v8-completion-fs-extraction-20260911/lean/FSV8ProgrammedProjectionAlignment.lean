import FSV8V7ProgrammedAlignment
import FSV8V7HistoryProjectionAlignment
import FSV8V7WholeScriptUniformLaw

/-!
# Constructing the finite-script view of a programmed V7 oracle

Extraction replay states contain programmed challenge entries.  Their later
verifier reads are cache hits and consume no fresh random-oracle answer.  This
leaf constructs the generalized script-state alignment from chronological V7
history, cache and a concrete master fresh-answer tape without assuming
`NoProgrammed`.

The primary constructor keeps the actual finite tape explicit.  A padded-tape
corollary is only an existence/control result; it is not the random-oracle law
used by the eventual Fiat--Shamir theorem.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.FSV8ProgrammedProjectionAlignment

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSFreshTapeTrace
open FSV8V7HistoryProjectionAlignment FSV8V7WholeScriptUniformLaw

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- Exact operational facts needed at a verifier boundary.  Programmed table
entries are allowed; only genuinely fresh history records are matched to the
master tape. -/
structure ProjectionFacts {steps : Nat}
    (tape : Tape) (finiteTape : FreshAnswerTape Block steps)
    (state : OracleState) : Prop where
  historyTotal : state.history.length = state.totalCalls
  freshCount : FreshHistoryCountCoherent state
  tapeMatches : FreshHistoryMatchesTape finiteTape state
  withinTape : WithinFreshAnswerTape finiteTape state
  tapeCompatibility : ∀ i (h : i < steps),
    tape i = (freshAnswerTapeToList finiteTape).get
      ⟨i, by simpa using h⟩

/-- The projected finite-script state preserves programmed cache entries but
marks their reads non-fresh. -/
theorem project_state_aligned {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps} {state : OracleState}
    (facts : ProjectionFacts tape finiteTape state) :
    FSV8V7ProgrammedAlignment.StateAligned tape finiteTape state
      (projectOracleState state) := by
  constructor
  · simpa [projectOracleState] using facts.historyTotal.symm
  · simp only [projectOracleState]
  · intro input
    rfl
  · rfl
  · change freshAnswers (state.history.map projectRecord) =
      (List.range state.freshCalls).map tape
    rw [projected_fresh_answers_eq_enumeration]
    have tapeEq := facts.tapeMatches
    unfold FreshHistoryMatchesTape at tapeEq
    rw [tapeEq]
    calc
      (freshAnswerTapeToList finiteTape).take state.freshCalls =
          (List.range state.freshCalls).map
            (extendFreshTape finiteTape (tape 0)) :=
        extended_tape_projected_prefix finiteTape
          (tape 0) state.freshCalls facts.withinTape.2
      _ = (List.range state.freshCalls).map tape := by
        apply List.map_congr_left
        intro i member
        have bound : i < steps := lt_of_lt_of_le
          (List.mem_range.mp member) facts.withinTape.2
        exact (extendFreshTape_compatible finiteTape (tape 0) i bound).trans
          (facts.tapeCompatibility i bound).symm
  · exact facts.freshCount
  · exact facts.tapeMatches
  · exact facts.withinTape
  · exact facts.tapeCompatibility

/-- The projected-state tape trace in the form used by `StateAligned`. -/
theorem projected_tape_prefix {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps} {state : OracleState}
    (facts : ProjectionFacts tape finiteTape state) :
    freshAnswers (projectOracleState state).log =
      (List.range (projectOracleState state).next).map tape :=
  (project_state_aligned facts).tapePrefix

/-- Any aligned programmed boundary can now use the exact structural compiler
theorem.  This is a deterministic bridge; uniformity of `finiteTape` is a
separate probabilistic premise supplied by the global ROM experiment. -/
theorem run_from_projected_state_aligned
    {A : Type} {steps n : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    (script : Script Bytes Block A n) (state : OracleState)
    (facts : ProjectionFacts tape finiteTape state)
    (totalRoom : state.totalCalls + n ≤ limits.totalCalls)
    (freshRoom : state.freshCalls + n ≤ limits.freshCalls)
    (tapeRoom : (projectOracleState state).next + n ≤ steps) :
    let machine := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor n state (FSV8V7OracleMachineBridge.compileScript script)
    FSV8V7ProgrammedAlignment.ResultAligned
        (run tape script (projectOracleState state)).1 machine.halt ∧
      FSV8V7ProgrammedAlignment.StateAligned tape finiteTape machine.oracle
        (run tape script (projectOracleState state)).2 := by
  exact FSV8V7ProgrammedAlignment.run_compileScript_aligned limits actor script
    state (projectOracleState state) (project_state_aligned facts)
      totalRoom freshRoom tapeRoom

#print axioms project_state_aligned
#print axioms projected_tape_prefix
#print axioms run_from_projected_state_aligned

end AspisV8Completion.FSV8ProgrammedProjectionAlignment
