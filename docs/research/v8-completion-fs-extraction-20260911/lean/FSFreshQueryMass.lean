import Mathlib
import FSFirstFresh

/-!
The local probability law for the *actual* lazy-oracle `query` transition.

This file deliberately stops at one cache miss.  It does not assert that a
particular Aspis squeeze input is new, nor that the OOD decoder sees four
independent blocks.  Those are source-order obligations.  What it removes is
the separate gap between an unseen source query and the uniform finite coin
used by the existing retry-mass development.
-/
set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSFreshQueryMass
open scoped BigOperators
open FSOracleExecution
noncomputable section

universe u v
variable {I : Type u} {O : Type v} [DecidableEq I]

/-- Change only the next unread tape cell.  Earlier and later cells retain
their values, which is the coupling needed at an adaptive source prefix. -/
def installNext (tape : Nat → O) (next : Nat) (coin : O) : Nat → O :=
  fun index => if index = next then coin else tape index

@[simp] theorem installNext_at (tape : Nat → O) (next : Nat) (coin : O) :
    installNext tape next coin next = coin := by
  simp [installNext]

theorem installNext_away (tape : Nat → O) (next index : Nat) (coin : O)
    (different : index ≠ next) :
    installNext tape next coin index = tape index := by
  simp [installNext, different]

/-- On a literal cache miss, the actual interpreter's returned answer is the
coin installed at the current unread tape position.  No transcript or
decoder abstraction occurs in this statement. -/
theorem query_miss_answer (tape : Nat → O) (state : State I O) (input : I)
    (coin : O) (miss : state.cache input = none) :
    (query (installNext tape state.next coin) state input).1 = coin := by
  simp [query, miss, installNext]

theorem query_miss_next (tape : Nat → O) (state : State I O) (input : I)
    (coin : O) (miss : state.cache input = none) :
    (query (installNext tape state.next coin) state input).2.next = state.next + 1 := by
  simp [query, miss]

/-- Reachable cache completeness turns a genuinely unseen input into a cache
miss.  This is the missing logical direction needed before using a fresh-coin
law; log/cache coherence alone would not suffice. -/
theorem cache_miss_of_unseen (state : FSFirstFresh.Oracle)
    (valid : FSFirstFresh.ValidHistory state) (input : List UInt8)
    (unseen : input ∉ FSExposureOrder.inputs state.log) :
    state.cache input = none := by
  cases found : state.cache input with
  | none => rfl
  | some answer =>
      exact False.elim (unseen (valid.complete input answer found))

/-- Exact uniform target mass at every cache-miss state.  The state and input
may have been chosen adaptively from the complete prior history. -/
theorem query_miss_uniform_target [Fintype O] [Nonempty O] [DecidableEq O]
    (tape : Nat → O) (state : State I O) (input : I)
    (miss : state.cache input = none) (target : O) :
    (∑ coin : O,
      if (query (installNext tape state.next coin) state input).1 = target
      then (1 : ℚ) else 0) / Fintype.card O =
        1 / Fintype.card O := by
  simp only [query_miss_answer tape state input _ miss]
  simp

/-- Source-facing form: at any valid adaptive history, an input absent from
the actual chronological log receives exact uniform target mass.  No caller
supplies a cache-miss hypothesis. -/
theorem unseen_query_uniform_target
    (tape : Nat → FSExposureOrder.Block)
    (state : FSFirstFresh.Oracle) (input : List UInt8)
    (valid : FSFirstFresh.ValidHistory state)
    (unseen : input ∉ FSExposureOrder.inputs state.log)
    (target : FSExposureOrder.Block) :
    (∑ coin : FSExposureOrder.Block,
      if (query (installNext tape state.next coin) state input).1 = target
      then (1 : ℚ) else 0) / Fintype.card FSExposureOrder.Block =
        1 / Fintype.card FSExposureOrder.Block :=
  query_miss_uniform_target tape state input
    (cache_miss_of_unseen state valid input unseen) target

/-- A cached query has no coin-dependent mass: changing the unread tape cell
cannot create a new independent draw. -/
theorem query_hit_coin_independent (tape : Nat → O) (state : State I O)
    (input : I) (answer coin left : O)
    (hit : state.cache input = some answer) :
    query (installNext tape state.next coin) state input =
      query (installNext tape state.next left) state input := by
  simp [query, hit]

#print axioms query_miss_answer
#print axioms cache_miss_of_unseen
#print axioms query_miss_uniform_target
#print axioms unseen_query_uniform_target
#print axioms query_hit_coin_independent

end
end AspisV8Completion.FSFreshQueryMass
