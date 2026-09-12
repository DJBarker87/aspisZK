/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.OracleCache
variable {I O : Type*} [DecidableEq I]

structure State (I O : Type*) where
  cache : I → Option O
  fresh : Nat
  calls : Nat

/-- Coins are consumed only by the none branch. An actual lazy-ROM
semantics must additionally supply the law of those fresh coins. -/
def query (s : State I O) (input : I) (coin : O) : O × State I O :=
  match s.cache input with
  | some cached => (cached, {s with calls := s.calls+1})
  | none => (coin, ⟨Function.update s.cache input (some coin), s.fresh+1, s.calls+1⟩)

theorem cached_answer (s : State I O) (input : I) (old coin : O)
    (hit : s.cache input = some old) :
    (query s input coin).1 = old ∧
    (query s input coin).2.fresh = s.fresh := by
  simp [query, hit]

theorem fresh_answer (s : State I O) (input : I) (coin : O)
    (miss : s.cache input = none) :
    (query s input coin).1 = coin ∧
    (query s input coin).2.cache input = some coin ∧
    (query s input coin).2.fresh = s.fresh+1 := by
  simp [query, miss]

theorem other_cached_preserved (s : State I O) (input other : I) (coin : O)
    (different : other ≠ input) :
    (query s input coin).2.cache other = s.cache other := by
  cases hit : s.cache input <;> simp [query, hit, different, Ne.symm different]

theorem calls_increment (s : State I O) (input : I) (coin : O) :
    (query s input coin).2.calls = s.calls+1 := by
  cases hit : s.cache input <;> simp [query, hit]

/-- Replaying a cache hit cannot generate a fresh independent challenge. -/
theorem cached_coin_irrelevant (s : State I O) (input : I) (old a b : O)
    (hit : s.cache input = some old) : query s input a = query s input b := by
  simp [query, hit]

#print axioms cached_coin_irrelevant
#print axioms other_cached_preserved
end AspisV8Completion.OracleCache
