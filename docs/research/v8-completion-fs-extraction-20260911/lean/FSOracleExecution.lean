import Std
set_option autoImplicit false

namespace AspisV8Completion.FSOracleExecution
universe u v w
variable {I : Type u} {O : Type v} {A : Type w} [DecidableEq I]

structure Event (I : Type u) (O : Type v) where
  input : I
  answer : O
  fresh : Bool

/-- Full answers, including adversary-first answers, remain in one shared log.
The initial cache/log consistency is an environment obligation, not erased. -/
structure State (I : Type u) (O : Type v) where
  cache : I → Option O
  next : Nat
  log : List (Event I O)

def query (tape : Nat → O) (s : State I O) (input : I) : O × State I O :=
  match s.cache input with
  | some answer => (answer, { s with log := s.log ++ [⟨input, answer, false⟩] })
  | none =>
      let answer := tape s.next
      (answer, ⟨(fun i => if i = input then some answer else s.cache i),
        s.next + 1, s.log ++ [⟨input, answer, true⟩]⟩)

theorem query_log (tape : Nat → O) (s : State I O) (input : I) :
    ∃ event, (query tape s input).2.log = s.log ++ [event] ∧
      event.input = input ∧ event.answer = (query tape s input).1 := by
  cases h : s.cache input <;> simp [query, h]

theorem cache_hit_ignores_tape (left right : Nat → O) (s : State I O)
    (input : I) (answer : O) (hit : s.cache input = some answer) :
    query left s input = query right s input ∧ (query left s input).2.next = s.next := by
  simp [query, hit]

theorem answer_installed (tape : Nat → O) (s : State I O) (input : I) :
    (query tape s input).2.cache input = some (query tape s input).1 := by
  cases h : s.cache input <;> simp [query, h]

theorem query_next_bound (tape : Nat → O) (s : State I O) (input : I) :
    s.next ≤ (query tape s input).2.next ∧ (query tape s input).2.next ≤ s.next + 1 := by
  cases h : s.cache input <;> simp [query, h]

def CacheConsistent (hash : I → O) (s : State I O) : Prop :=
  ∀ input answer, s.cache input = some answer → answer = hash input

/-- Deterministic coupling to a fixed hash function, not a random-oracle law.
The backing hash is evaluated only as the answer at the current input. -/
def queryHash (hash : I → O) (s : State I O) (input : I) : O × State I O :=
  query (fun _ => hash input) s input

theorem queryHash_refines (hash : I → O) (s : State I O) (input : I)
    (consistent : CacheConsistent hash s) :
    (queryHash hash s input).1 = hash input ∧
    CacheConsistent hash (queryHash hash s input).2 := by
  cases h : s.cache input with
  | some answer =>
      constructor
      · simpa [queryHash, query, h] using consistent input answer h
      · simpa [CacheConsistent, queryHash, query, h] using consistent
  | none =>
      constructor
      · simp [queryHash, query, h]
      · intro other answer hit
        simp only [queryHash, query, h] at hit
        split at hit
        · cases hit; congr 1; symm; assumption
        · exact consistent other answer hit

theorem old_answer_preserved (tape : Nat → O) (s : State I O) (input old : I)
    (answer : O) (hit : s.cache old = some answer) :
    (query tape s input).2.cache old = some answer := by
  cases h : s.cache input with
  | some a => simpa [query, h] using hit
  | none =>
    have ne : old ≠ input := by intro eq; subst old; simp [h] at hit
    simpa [query, h, ne] using hit

/-- A bounded causal strategy. A failed sampler remains an explicit abort,
and a shorter successful path does not consume unused tape entries. -/
inductive Script (I : Type u) (O : Type v) (A : Type w) : Nat → Type (max u v w)
  | done {n : Nat} (value : A) : Script I O A n
  | abort {n : Nat} : Script I O A n
  | ask {n : Nat} (input : I) (next : O → Script I O A n) : Script I O A (n+1)

def run (tape : Nat → O) : {n : Nat} → Script I O A n → State I O → Option A × State I O
  | _, .done value, s => (some value, s)
  | _, .abort, s => (none, s)
  | _, .ask input next, s =>
      let step := query tape s input
      run tape (next step.1) step.2

/-- Both successful and aborting runs extend the actual log. This constructs
the shared history, rather than assuming answer-log membership. -/
theorem run_extends (tape : Nat → O) : ∀ {n : Nat} (p : Script I O A n) (s : State I O),
    ∃ suffix, (run tape p s).2.log = s.log ++ suffix := by
  intro n p
  induction p with
  | done value => intro s; exact ⟨[], by simp [run]⟩
  | abort => intro s; exact ⟨[], by simp [run]⟩
  | ask input next ih =>
      intro s
      obtain ⟨e, he, _, _⟩ := query_log tape s input
      obtain ⟨tail, ht⟩ := ih (query tape s input).1 (query tape s input).2
      exact ⟨e :: tail, by simpa [run, he, List.append_assoc] using ht⟩

theorem run_preserves_answer (tape : Nat → O) : ∀ {n : Nat} (p : Script I O A n)
    (s : State I O) (input : I) (answer : O), s.cache input = some answer →
    (run tape p s).2.cache input = some answer := by
  intro n p
  induction p with
  | done value => intro s input answer hit; exact hit
  | abort => intro s input answer hit; exact hit
  | ask requested next ih =>
      intro s input answer hit
      apply ih (query tape s requested).1 (query tape s requested).2 input answer
      exact old_answer_preserved tape s requested input answer hit

theorem retained_prefix (tape : Nat → O) {n : Nat} (p : Script I O A n) (s : State I O) :
    (run tape p s).2.log.take s.log.length = s.log := by
  obtain ⟨suffix, h⟩ := run_extends tape p s
  rw [h]
  simp

theorem call_bound (tape : Nat → O) : ∀ {n : Nat} (p : Script I O A n) (s : State I O),
    (run tape p s).2.log.length ≤ s.log.length + n := by
  intro n p
  induction p with
  | done value => intro s; simp [run]
  | abort => intro s; simp [run]
  | @ask n input next ih =>
      intro s
      have h := ih (query tape s input).1 (query tape s input).2
      obtain ⟨e, he, _, _⟩ := query_log tape s input
      simp only [he, List.length_append, List.length_cons, List.length_nil] at h
      simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Prefix-fixed replies can be transported between tapes WITHOUT assuming
freshness. The premise refers only to replies actually consumed on the left.
It is a deterministic coupling lemma, not a law for random tapes. -/
theorem run_tape_congr (left right : Nat → O) : ∀ {n : Nat} (p : Script I O A n)
    (s : State I O),
    (∀ j, s.next ≤ j → j < s.next + n → left j = right j) →
    run left p s = run right p s := by
  intro n p
  induction p with
  | done value => intro s same; rfl
  | abort => intro s same; rfl
  | @ask n input next ih =>
      intro s same
      have step : query left s input = query right s input := by
        cases hit : s.cache input with
        | some answer => simp [query, hit]
        | none => simp [query, hit, same s.next (by omega) (by omega)]
      simp only [run]
      rw [← step]
      apply ih (query left s input).1 (query left s input).2
      intro j lo hi
      cases hit : s.cache input <;> simp [query, hit] at lo hi <;> apply same j <;> omega

#print axioms run_extends
#print axioms run_preserves_answer
#print axioms retained_prefix
#print axioms call_bound
#print axioms run_tape_congr
#print axioms queryHash_refines
end AspisV8Completion.FSOracleExecution
