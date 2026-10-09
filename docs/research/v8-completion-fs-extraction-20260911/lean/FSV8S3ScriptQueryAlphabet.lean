import FSOracleExecution
import FSTranscriptScript

/-! S3 FIRST-ATTEMPT SOURCE MODULE. Not compiled in the preparation environment.
The statement and its proof body must be checked against the pinned checkout.
A local lemma is not a global soundness claim. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace AspisV8Completion.FSV8S3ScriptQueryAlphabet
open FSOracleExecution
universe u v w
variable {I : Type u} {O : Type v} {A : Type w} [DecidableEq I]

/-- Universal over oracle answers; not a trace sample or a list of allowed
queries assumed to cover the chosen run. The constructors follow Script. -/
def QueriesIn (P : I → Prop) : {n : Nat} → Script I O A n → Prop
  | _, .done _ => True
  | _, .abort => True
  | _, .ask input next => P input ∧ ∀ answer, QueriesIn P (next answer)

/-- Establishes the exact new event suffix, its alphabet, and its size together.
Cached and fresh queries both append a record; aborts keep their actual prefix. -/
theorem run_has_safe_bounded_suffix
    (P : I → Prop) (tape : Nat → O) :
    ∀ {n : Nat} (script : Script I O A n) (initial : State I O),
      QueriesIn P script →
      ∃ suffix : List (Event I O),
        (run tape script initial).2.log = initial.log ++ suffix ∧
        (∀ event ∈ suffix, P event.input) ∧ suffix.length ≤ n := by
  intro n script
  induction script with
  | done value =>
    intro initial _
    exact ⟨[], by simp [run], by simp, by simp⟩
  | abort =>
    intro initial _
    exact ⟨[], by simp [run], by simp, by simp⟩
  | @ask remaining input next ih =>
    intro initial safe
    rcases safe with ⟨inputSafe, nextSafe⟩
    let first := query tape initial input
    obtain ⟨event, eventLog, eventInput, eventAnswer⟩ := query_log tape initial input
    obtain ⟨suffix, tailLog, tailSafe, tailLength⟩ :=
      ih first.1 first.2 (nextSafe first.1)
    refine ⟨event :: suffix, ?_, ?_, ?_⟩
    · change (run tape (next first.1) first.2).2.log = _
      rw [tailLog, eventLog]
      simp [List.append_assoc]
    · intro e member
      rcases List.mem_cons.mp member with rfl | rest
      · simpa only [eventInput] using inputSafe
      · exact tailSafe e rest
    · simp only [List.length_cons]
      omega

/-- Query-alphabet weakening has no execution or probability assumption. -/
theorem QueriesIn.mono (P Q : I → Prop)
    (imp : ∀ input, P input → Q input) :
    ∀ {n} (script : Script I O A n), QueriesIn P script → QueriesIn Q script := by
  intro n script
  induction script with
  | done => intro _; trivial
  | abort => intro _; trivial
  | ask input next ih =>
    intro safe
    exact ⟨imp input safe.1, fun answer => ih answer (safe.2 answer)⟩

#print axioms run_has_safe_bounded_suffix
#print axioms QueriesIn.mono
end AspisV8Completion.FSV8S3ScriptQueryAlphabet
