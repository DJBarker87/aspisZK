import FSV8V7HistoryProjectionAlignment
import FSV8V7FiniteUniformBridge

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8WellFormedFreshOracle
open FSOracleExecution FSBoundedTranscript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSV8V7StateAlignment
open FSV8V7HistoryProjectionAlignment
open FSV8V7FiniteUniformBridge
open FSV8V7WholeScriptUniformLaw

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block

def NoDuplicateInputs (state : OracleState) : Prop :=
  ∀ a ∈ state.table, ∀ b ∈ state.table, a.input = b.input → a = b

structure WellFormedFreshOracle (state : OracleState) : Prop where
  historyTotal : state.history.length = state.totalCalls
  freshCount : FreshHistoryCountCoherent state
  noProgrammed : NoProgrammed state
  noDuplicateInputs : NoDuplicateInputs state

def historyPaddedFin (state : OracleState) (fallback : Block)
    {steps : Nat} (_bound : state.freshCalls ≤ steps) : Fin steps → Block :=
  fun i => if h : i.val < (freshAnswerEnumeration state.history).length then
    (freshAnswerEnumeration state.history).get ⟨i.val, h⟩ else fallback

def historyPaddedTape (state : OracleState) (fallback : Block)
    {steps : Nat} (bound : state.freshCalls ≤ steps) :
    FreshAnswerTape Block steps :=
  finFreshEquiv steps (historyPaddedFin state fallback bound)

theorem historyPaddedTape_consumed_prefix (state : OracleState)
    (wellFormed : WellFormedFreshOracle state) (fallback : Block)
    {steps : Nat} (bound : state.freshCalls ≤ steps) :
    (freshAnswerTapeToList (historyPaddedTape state fallback bound)).take
        state.freshCalls =
      freshAnswerEnumeration state.history := by
  have count : (freshAnswerEnumeration state.history).length = state.freshCalls :=
    wellFormed.freshCount
  have listEq := finFreshEquiv_list steps (historyPaddedFin state fallback bound)
  change (freshAnswerTapeToList
    (finFreshEquiv steps (historyPaddedFin state fallback bound))).take
      state.freshCalls = freshAnswerEnumeration state.history
  rw [listEq]
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left bound, count]
  · intro i leftBound rightBound
    have iCalls : i < state.freshCalls := by
      simpa [List.length_take, Nat.min_eq_left bound, count] using leftBound
    simp only [List.getElem_take, List.getElem_ofFn]
    simp [historyPaddedFin, count, iCalls]

theorem wellFormed_projected_state_aligned (state : OracleState)
    (wellFormed : WellFormedFreshOracle state) (fallback : Block)
    {steps : Nat} (bound : state.freshCalls ≤ steps) :
    StateAligned (extendFreshTape (historyPaddedTape state fallback bound) fallback)
      (historyPaddedTape state fallback bound) state (projectOracleState state) := by
  let finiteTape := historyPaddedTape state fallback bound
  let tape := extendFreshTape finiteTape fallback
  have consumed := historyPaddedTape_consumed_prefix state wellFormed fallback bound
  have projected := projected_fresh_answers_eq_enumeration state.history
  have rangePrefix := extended_tape_projected_prefix finiteTape fallback
    state.freshCalls bound
  have projectedPrefix :
      FSFreshTapeTrace.freshAnswers (state.history.map projectRecord) =
        (List.range state.freshCalls).map tape := by
    rw [projected, ← consumed, rangePrefix]
  have facts : FreshOnlyProjectionFacts tape finiteTape state := by
    refine ⟨wellFormed.historyTotal, wellFormed.noProgrammed, wellFormed.freshCount,
      ?_, ?_, projectedPrefix, ?_⟩
    · exact consumed.symm
    · exact ⟨wellFormed.freshCount, bound⟩
    · exact extendFreshTape_compatible finiteTape fallback
  exact project_state_aligned facts

theorem empty_wellFormed : WellFormedFreshOracle emptyOracle := by
  constructor <;> simp [emptyOracle, NoProgrammed, NoDuplicateInputs]
  exact empty_oracle_fresh_history_count_coherent

theorem query_success_preserves_wellFormed
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : Bytes) (output : Block)
    (wellFormed : WellFormedFreshOracle state)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    WellFormedFreshOracle nextState := by
  constructor
  · exact query_success_preserves_history_total controller limits actor state
      nextState input output wellFormed.historyTotal success
  · exact query_oracle_success_preserves_fresh_history_count controller limits actor
      state nextState input output wellFormed.freshCount success
  · exact query_success_preserves_no_programmed controller limits actor state
      nextState input output wellFormed.noProgrammed success
  · unfold queryOracle at success
    split at success <;> try contradiction
    next _ =>
      split at success
      next entry _ =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at success
        rcases success with ⟨_, rfl⟩
        exact wellFormed.noDuplicateInputs
      next missing =>
        split at success <;> try contradiction
        next _ =>
          split at success <;> try contradiction
          next answer answered =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at success
            rcases success with ⟨_, rfl⟩
            intro a membershipA b membershipB equalInputs
            simp only [List.mem_append, List.mem_singleton] at membershipA membershipB
            rcases membershipA with oldA | rfl
            · rcases membershipB with oldB | rfl
              · exact wellFormed.noDuplicateInputs a oldA b oldB equalInputs
              · exfalso
                have missing' := List.find?_eq_none.mp missing
                exact missing' a oldA
                  (of_decide_eq_true (by simpa using equalInputs))
            · rcases membershipB with oldB | rfl
              · exfalso
                have missing' := List.find?_eq_none.mp missing
                exact missing' b oldB
                  (of_decide_eq_true (by simpa using equalInputs.symm))
              · rfl

theorem run_machine_preserves_wellFormed
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result)
    (wellFormed : WellFormedFreshOracle state) :
    WellFormedFreshOracle
      (runMachine controller limits actor fuel state program).oracle := by
  induction fuel generalizing state program with
  | zero => cases program <;> simpa [runMachine] using wellFormed
  | succ fuel ih =>
      cases program with
      | pure result => simpa [runMachine] using wellFormed
      | abort reason => simpa [runMachine] using wellFormed
      | query input next =>
          simp only [runMachine]
          cases queried : queryOracle controller limits actor state input with
          | error reason => simpa using wellFormed
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              have nextWellFormed := query_success_preserves_wellFormed controller
                limits actor state nextState input output wellFormed queried
              simpa using ih nextState (next output) nextWellFormed

theorem run_from_empty_projected_state_aligned
    {Result : Type*} (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (program : OracleMachine Result)
    (fallback : Block) {steps : Nat}
    (bound : (runMachine controller limits actor fuel emptyOracle program).oracle.freshCalls
      ≤ steps) :
    StateAligned
        (extendFreshTape
          (historyPaddedTape
            (runMachine controller limits actor fuel emptyOracle program).oracle
            fallback bound) fallback)
        (historyPaddedTape
          (runMachine controller limits actor fuel emptyOracle program).oracle
          fallback bound)
        (runMachine controller limits actor fuel emptyOracle program).oracle
        (projectOracleState
          (runMachine controller limits actor fuel emptyOracle program).oracle) := by
  apply wellFormed_projected_state_aligned _ _ fallback bound
  exact run_machine_preserves_wellFormed controller limits actor fuel emptyOracle
    program empty_wellFormed

#print axioms empty_wellFormed
#print axioms query_success_preserves_wellFormed
#print axioms run_machine_preserves_wellFormed
#print axioms historyPaddedTape_consumed_prefix
#print axioms wellFormed_projected_state_aligned
#print axioms run_from_empty_projected_state_aligned
end AspisV8Completion.FSV8WellFormedFreshOracle
