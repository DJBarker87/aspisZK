import FSV8V7OracleMachineBridge

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8V7StateAlignment
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSFreshTapeTrace

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

def NoProgrammed (v7 : OracleState) : Prop :=
  ∀ entry ∈ v7.table, entry.source = .fresh

structure StateAligned {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps)
    (v7 : OracleState) (fs : State Bytes Block) : Prop where
  totalCalls : v7.totalCalls = fs.log.length
  freshCalls : v7.freshCalls = fs.next
  cache : ∀ input, fs.cache input = (lookupEntry v7 input).map TableEntry.output
  history : fs.log = v7.history.map projectRecord
  tapePrefix : freshAnswers fs.log = (List.range fs.next).map tape
  noProgrammed : NoProgrammed v7
  coherent : FreshHistoryCountCoherent v7
  tapeMatches : FreshHistoryMatchesTape finiteTape v7
  withinTape : WithinFreshAnswerTape finiteTape v7
  tapeCompatibility : ∀ i (h : i < steps),
    tape i = (freshAnswerTapeToList finiteTape).get
      ⟨i, by simpa using h⟩

theorem empty_aligned {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps)
    (compatibility : ∀ i (h : i < steps),
      tape i = (freshAnswerTapeToList finiteTape).get
        ⟨i, by simpa using h⟩) :
    StateAligned tape finiteTape emptyOracle
      (FSFirstFresh.empty : State Bytes Block) := by
  constructor
  · rfl
  · rfl
  · intro input; rfl
  · rfl
  · rfl
  · simp [NoProgrammed, emptyOracle]
  · exact empty_oracle_fresh_history_count_coherent
  · exact empty_oracle_fresh_history_matches_tape finiteTape
  · exact empty_oracle_within_fresh_answer_tape finiteTape
  · exact compatibility

/- The final recursive run theorem remains open until the one-step premises
   are supplied by a controller/limits refinement. In particular, this leaf
   does not identify programmed V7 entries with the unprogrammed Script model.
-/
#print axioms empty_aligned
end AspisV8Completion.FSV8V7StateAlignment
