import FSOracleExecution

/-!
Exact fresh-answer trace of the current bounded lazy-oracle interpreter.

Cached calls remain in the chronological event log but consume no tape entry.
For every execution, filtering the log to fresh events yields exactly the
prefix `tape 0, ..., tape (next-1)`.  This is the deterministic bridge needed
before applying the existing V7 uniform finite-tape probability machinery;
it is not itself a random-oracle probability theorem.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSFreshTapeTrace
open FSOracleExecution

universe u v w
variable {I : Type u} {O : Type v} {A : Type w} [DecidableEq I]

def freshAnswers (log : List (Event I O)) : List O :=
  log.filterMap fun event => if event.fresh then some event.answer else none

def MatchesTape (tape : Nat → O) (state : State I O) : Prop :=
  freshAnswers state.log = (List.range state.next).map tape

theorem empty_matches (tape : Nat → O) :
    MatchesTape tape (⟨fun _ : I => none, 0, []⟩ : State I O) := by
  rfl

theorem query_matches (tape : Nat → O) (state : State I O) (input : I)
    (matched : MatchesTape tape state) :
    MatchesTape tape (query tape state input).2 := by
  cases hit : state.cache input with
  | some answer =>
      simpa [query, hit, MatchesTape, freshAnswers] using matched
  | none =>
      simp only [query, hit, MatchesTape, freshAnswers, List.filterMap_append,
        List.filterMap_cons, List.filterMap_nil, ↓reduceIte,
        List.map_append, List.range_succ]
      simpa [matched]

/-- A whole causal script, including an aborting one, preserves the exact
fresh-tape trace.  No success, cache-miss or fixed-query-order premise is
required. -/
theorem run_matches (tape : Nat → O) :
    ∀ {n : Nat} (program : Script I O A n) (state : State I O),
      MatchesTape tape state → MatchesTape tape (run tape program state).2 := by
  intro n program
  induction program with
  | done value => intro state matched; exact matched
  | abort => intro state matched; exact matched
  | ask input next ih =>
      intro state matched
      exact ih (query tape state input).1 (query tape state input).2
        (query_matches tape state input matched)

theorem run_from_empty_matches (tape : Nat → O) {n : Nat}
    (program : Script I O A n) :
    MatchesTape tape
      (run tape program (⟨fun _ : I => none, 0, []⟩ : State I O)).2 :=
  run_matches tape program _ (empty_matches (I := I) tape)

#print axioms empty_matches
#print axioms query_matches
#print axioms run_matches
#print axioms run_from_empty_matches

end AspisV8Completion.FSFreshTapeTrace
