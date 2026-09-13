import FSTranscriptScript

/-!
S5 FIRST ATTEMPT, NOT COMPILED IN THE HANDOFF ENVIRONMENT.
Syntax-directed query coverage for the existing Script, including aborts and
cache hits. This is not a probability theorem. It does not replace validation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
namespace AspisV8Completion.FSV8S5ScriptQueryAlphabet
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
abbrev Bytes := List UInt8
variable {A B : Type}

/-- Universal in answers; no sampled-run-only alphabet assumption. -/
def AllInputs (allowed : Bytes → Prop) :
    {n : Nat} → Script Bytes Block A n → Prop
  | _, .done _ => True
  | _, .abort => True
  | _, .ask input next => allowed input ∧ ∀ answer, AllInputs allowed (next answer)

theorem allInputs_promote (allowed : Bytes → Prop) :
    ∀ {n} (p : Script Bytes Block A n), AllInputs allowed p →
      AllInputs allowed (promote p) := by
  intro n p
  induction p with
  | done => intro _; trivial
  | abort => intro _; trivial
  | ask input next ih =>
      intro h
      exact ⟨h.1, fun answer => ih answer (h.2 answer)⟩

theorem allInputs_pad (allowed : Bytes → Prop) {n}
    (p : Script Bytes Block A n) (h : AllInputs allowed p) (extra : Nat) :
    AllInputs allowed (pad p extra) := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact allInputs_promote allowed _ ih

theorem allInputs_map (allowed : Bytes → Prop) {n}
    (p : Script Bytes Block A n) (f : A → B) (h : AllInputs allowed p) :
    AllInputs allowed (map f p) := by
  revert h
  induction p with
  | done => intro _; trivial
  | abort => intro _; trivial
  | ask input next ih => intro h; exact ⟨h.1, fun answer => ih answer (h.2 answer)⟩

theorem allInputs_bind (allowed : Bytes → Prop) {m} :
    ∀ {n} (p : Script Bytes Block A n)
      (next : A → Script Bytes Block B m),
      AllInputs allowed p → (∀ a, AllInputs allowed (next a)) →
        AllInputs allowed (bind p next) := by
  intro n p
  induction p with
  | done a =>
      intro next _ hnext
      exact allInputs_pad allowed _ (hnext a) _
  | abort => intro next _ _; trivial
  | ask input response ih =>
      intro next hp hnext
      exact ⟨hp.1, fun answer => ih answer next (hp.2 answer) hnext⟩

/-- The actual appended log satisfies the alphabet, not just its fresh projection. -/
theorem run_appends_only_allowed (allowed : Bytes → Prop) (tape : Tape) :
    ∀ {n} (p : Script Bytes Block A n) (s : Oracle),
      AllInputs allowed p →
      ∃ suffix,
        (run tape p s).2.log = s.log ++ suffix ∧
        ∀ event ∈ suffix, allowed event.input := by
  intro n p
  induction p with
  | done value =>
      intro s _
      exact ⟨[], by simp [run], by simp⟩
  | abort =>
      intro s _
      exact ⟨[], by simp [run], by simp⟩
  | ask input next ih =>
      intro s hp
      obtain ⟨event, eventLog, eventInput, _⟩ := query_log tape s input
      obtain ⟨tail, tailLog, tailAllowed⟩ :=
        ih (query tape s input).1 (query tape s input).2
          (hp.2 (query tape s input).1)
      refine ⟨event :: tail, ?_, ?_⟩
      · simpa [run, eventLog, List.append_assoc] using tailLog
      · intro e member
        rcases List.mem_cons.mp member with h | h
        · subst e
          rw [eventInput]
          exact hp.1
        · exact tailAllowed e h

/-- Upward closure is a syntax proof and has no oracle assumptions. -/
theorem allInputs_mono (p : Bytes → Prop) (q : Bytes → Prop)
    (imp : ∀ input, p input → q input) :
    ∀ {n} (script : Script Bytes Block A n),
      AllInputs p script → AllInputs q script := by
  intro n script
  induction script with
  | done => intro _; trivial
  | abort => intro _; trivial
  | ask input next ih =>
      intro h
      exact ⟨imp input h.1, fun answer => ih answer (h.2 answer)⟩

#print axioms run_appends_only_allowed
#print axioms allInputs_bind
end AspisV8Completion.FSV8S5ScriptQueryAlphabet
