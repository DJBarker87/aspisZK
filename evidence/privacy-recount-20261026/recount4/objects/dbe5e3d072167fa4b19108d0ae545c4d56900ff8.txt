import R1Z.ProverCommitOracleEffect26
/-! Explicit CoinOracle effects. This interface supplements, and does not
silently reinterpret, the old pure generated Digest32 dictionaries.
The ordered-map operation is the named D133 std contract. -/
set_option autoImplicit false
namespace R1Z.ProverCommitCoinTape27
open Aeneas Aeneas.Std Result

structure State (Key Answer : Type) where
  coins : Nat → Answer
  cursor : Nat
  record : Option (Key → Option Answer)
  collision : Bool

variable {Key Answer : Type} [DecidableEq Key] [DecidableEq Answer]

def insert (table : Key → Option Answer) (key : Key) (answer : Answer) :
    Option Answer × (Key → Option Answer) :=
  (table key,fun q => if q = key then some answer else table q)

/-- Control order of the shipped body, after the named map contract. -/
def native (s : State Key Answer) (key : Key) : Answer × State Key Answer :=
  let answer := s.coins s.cursor
  let advanced := {s with cursor := s.cursor+1}
  match advanced.record with
  | none => (answer,advanced)
  | some table =>
    let (previous,table') := insert table key answer
    let flagged := match previous with
      | none => advanced.collision
      | some old => if old ≠ answer then true else advanced.collision
    (answer,{advanced with record := some table',collision := flagged})

/-- Explicit returned effects; no mutable handle is hidden in the digest. -/
def reference (s : State Key Answer) (key : Key) : Answer × State Key Answer :=
  let answer := s.coins s.cursor
  (answer,⟨s.coins,s.cursor+1,
    s.record.map (fun t q => if q = key then some answer else t q),
    s.collision || (match s.record.bind (fun t => t key) with
      | none => false
      | some old => decide (old ≠ answer))⟩)

theorem call_preserves (s : State Key Answer) (key : Key) :
    native s key = reference s key := by
  rcases s with ⟨coins,cursor,record,collision⟩
  cases record with
  | none => simp [native,reference]
  | some table =>
    cases old : table key with
    | none => simp [native,reference,insert,old]
    | some previous =>
      by_cases h : previous = coins cursor
      · simp [native,reference,insert,old,h]
      · simp [native,reference,insert,old,h]

/-- Arbitrary finite adaptive call trees, including early exits. -/
inductive Program (Key Answer Value : Type) where
  | done : Value → Program Key Answer Value
  | call : Key → (Answer → Program Key Answer Value) → Program Key Answer Value

structure Execution (Key Answer Value : Type) where
  value : Value
  state : State Key Answer
  history : List (Key × Answer)

def run {Value : Type} (step : State Key Answer → Key → Answer × State Key Answer) :
    Program Key Answer Value → State Key Answer → Execution Key Answer Value
  | .done value,s => ⟨value,s,[]⟩
  | .call key next,s =>
    let (answer,s') := step s key
    let tail := run step (next answer) s'
    {tail with history := (key,answer)::tail.history}

/-- Full final state and ordered history, not just the returned digests. -/
theorem sequence_preserves {Value : Type} (p : Program Key Answer Value)
    (s : State Key Answer) : run native p s = run reference p s := by
  induction p generalizing s with
  | done value => rfl
  | call key next ih =>
    simp only [run,call_preserves]
    exact congrArg (fun tail : Execution Key Answer Value =>
      {tail with history := (key,(reference s key).1)::tail.history})
      (ih (reference s key).1 (reference s key).2)

/-- The cursor counts every query, including duplicates and exhausted reads. -/
theorem cursor_history {Value : Type} (p : Program Key Answer Value)
    (s : State Key Answer) :
    (run reference p s).state.cursor = s.cursor + (run reference p s).history.length := by
  induction p generalizing s with
  | done value => simp [run]
  | call key next ih =>
    have h := ih (reference s key).1 (reference s key).2
    simp only [run,List.length_cons]
    change (run reference (next (reference s key).1) (reference s key).2).state.cursor = _
    rw [h]
    simp only [reference]
    omega

/-- Stateful replacement of the generated semantic/circle/control hash API. -/
structure Digest32 (S : Type) where
  digest : S → ProverCommitOracleEffect26.Parts → Result (ProverCommitOracleEffect26.Bytes32 × S)

noncomputable def digest :
    Digest32 (State (List UInt8) ProverCommitOracleEffect26.Bytes32) := by
  classical
  exact ⟨fun s parts => ok (reference s (ProverCommitStreamBytes.wireBytes parts))⟩

/-- Finite native tapes retain the exact zero fallback. -/
def finite (zero : Answer) (coins : List Answer) : Nat → Answer :=
  fun cursor => (coins[cursor]?).getD zero

#print axioms call_preserves
#print axioms sequence_preserves
#print axioms cursor_history
end R1Z.ProverCommitCoinTape27
