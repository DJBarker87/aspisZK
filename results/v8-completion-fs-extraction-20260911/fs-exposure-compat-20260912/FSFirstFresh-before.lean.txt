import FSExposureOrder
set_option autoImplicit false
namespace AspisV8Completion.FSFirstFresh
open FSOracleExecution FSExposureOrder
abbrev Oracle := State Bytes Block

/-- No cache answer may be silently imported without its chronological query. -/
def CacheLogged (s : Oracle) : Prop :=
  ∀ input answer, s.cache input = some answer → input ∈ inputs s.log

/-- This chronology invariant is constructed by the query interpreter, not
assumed at the final first-exposure theorem. Initial histories may provide it
only with separate provenance; the empty state requires no premise. -/
def Flags (log : Log) : Prop := ∀ i (h : i < log.length),
  (log[i]'h).fresh = true ↔ (log[i]'h).input ∉ inputs (log.take i)

structure ValidHistory (s : Oracle) : Prop where
  coherent : LogConsistent s
  complete : CacheLogged s
  flags : Flags s.log

def empty : Oracle := ⟨fun _ => none, 0, []⟩
theorem empty_valid : ValidHistory empty := by
  constructor <;> simp [LogConsistent, CacheLogged, Flags, empty]

theorem query_cache_logged (tape : Nat → Block) (s : Oracle) (input : Bytes)
    (complete : CacheLogged s) : CacheLogged (query tape s input).2 := by
  intro other answer found
  cases h : s.cache input with
  | some cached =>
      have old : s.cache other = some answer := by simpa [query, h] using found
      have seen := complete other answer old
      simp only [query, h, inputs, List.map_append, List.map_cons, List.map_nil]
      exact List.mem_append.mpr (Or.inl seen)
  | none =>
      simp only [query, h] at found ⊢
      split at found
      · rename_i same
        subst other
        simp [inputs]
      · have seen := complete other answer found
        simpa [inputs] using (Or.inl seen : other ∈ inputs s.log ∨ other = input)

theorem flags_append (log : Log) (event : Event Bytes Block)
    (old : Flags log) (fresh : event.fresh = true ↔ event.input ∉ inputs log) :
    Flags (log ++ [event]) := by
  intro i hi
  by_cases before : i < log.length
  · simpa only [List.getElem_append_left before,
      List.take_append_of_le_length (Nat.le_of_lt before)] using old i before
  · have atEnd : i = log.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using fresh

theorem query_flags (tape : Nat → Block) (s : Oracle) (input : Bytes)
    (valid : ValidHistory s) : Flags (query tape s input).2.log := by
  cases h : s.cache input with
  | some answer =>
      simp only [query, h]
      apply flags_append s.log ⟨input, answer, false⟩ valid.flags
      have seen := valid.complete input answer h
      simp [seen]
  | none =>
      simp only [query, h]
      apply flags_append s.log ⟨input, tape s.next, true⟩ valid.flags
      have unseen : input ∉ inputs s.log := by
        intro seen
        obtain ⟨event, mem, eq⟩ := List.mem_map.mp seen
        have cached := valid.coherent event mem
        rw [eq, h] at cached
        contradiction
      simp [unseen]

theorem query_valid (tape : Nat → Block) (s : Oracle) (input : Bytes)
    (valid : ValidHistory s) : ValidHistory (query tape s input).2 :=
  ⟨query_log_consistent tape s input valid.coherent,
    query_cache_logged tape s input valid.complete, query_flags tape s input valid⟩

theorem run_valid {A : Type} (tape : Nat → Block) :
    ∀ {n : Nat} (program : Script Bytes Block A n) (s : Oracle),
    ValidHistory s → ValidHistory (run tape program s).2 := by
  intro n program
  induction program with
  | done value => intro s valid; exact valid
  | abort => intro s valid; exact valid
  | ask input next ih =>
      intro s valid
      exact ih (query tape s input).1 (query tape s input).2 (query_valid tape s input valid)

theorem first_fresh (s : Oracle) (valid : ValidHistory s) (input : Bytes)
    (seen : input ∈ inputs s.log) :
    ∃ h : firstExposure s.log input < s.log.length,
      (s.log[firstExposure s.log input]'h).fresh = true := by
  have within := List.idxOf_lt_length_of_mem seen
  have h : firstExposure s.log input < s.log.length := by
    simpa only [firstExposure, inputs, List.length_map] using within
  have found := List.getElem_idxOf within
  change (inputs s.log)[firstExposure s.log input] = input at found
  simp only [inputs, List.getElem_map] at found
  refine ⟨h, (valid.flags _ h).mpr ?_⟩
  rw [found]
  intro earlier
  have earlier' : input ∈ (inputs s.log).take ((inputs s.log).idxOf input) := by
    simpa only [inputs, List.map_take, firstExposure] using earlier
  have no := List.false_of_mem_take_findIdx (p := fun x => x == input) earlier'
  simp at no

/-- A concrete producer endpoint: no freshness/coherence predicate is supplied
by the caller. It is derived from actual bounded script execution from empty. -/
theorem first_fresh_from_empty {A : Type} {n : Nat} (tape : Nat → Block)
    (program : Script Bytes Block A n) (input : Bytes)
    (seen : input ∈ inputs (run tape program empty).2.log) :
    ∃ h : firstExposure (run tape program empty).2.log input <
        (run tape program empty).2.log.length,
      ((run tape program empty).2.log[firstExposure (run tape program empty).2.log input]'h).fresh = true :=
  first_fresh _ (run_valid tape program empty empty_valid) input seen

/-- The linked absorbed answer is now proved to belong to an ACTUAL fresh
first event. This joins the earlier source-byte ordering classifier without
assuming initial cache completeness, chronological flags, or final coherence.
All three invariants are constructed from the interpreter's empty start. -/
theorem linked_fresh_order_from_empty {A : Type} {n : Nat} (tape : Nat → Block)
    (program : Script Bytes Block A n) (state answer : Block) (label : UInt8) (message : Bytes)
    (linked : LinkedAbsorb (run tape program empty).2.log
      (absorbInput state label message) answer)
    (squeezed : squeezeInput answer ∈ inputs (run tape program empty).2.log) :
    (∃ h : firstExposure (run tape program empty).2.log (absorbInput state label message) <
        (run tape program empty).2.log.length,
      ((run tape program empty).2.log[firstExposure (run tape program empty).2.log
        (absorbInput state label message)]'h).answer = answer ∧
      ((run tape program empty).2.log[firstExposure (run tape program empty).2.log
        (absorbInput state label message)]'h).fresh = true) ∧
    (firstExposure (run tape program empty).2.log (absorbInput state label message) <
        firstExposure (run tape program empty).2.log (squeezeInput answer) ∨
      blockBytes answer ∈ priorTargets (run tape program empty).2.log
        (firstExposure (run tape program empty).2.log (absorbInput state label message))) := by
  have valid := run_valid tape program empty empty_valid
  obtain ⟨h, _, value⟩ := first_recorded_answer _ _ answer valid.coherent linked
  obtain ⟨_, fresh⟩ := first_fresh _ valid _ (seen_of_linked _ _ answer linked)
  exact ⟨⟨h, value, fresh⟩, linked_order_or_premature_target _ state answer label message linked squeezed⟩

private def zero : Block := fun _ => 0
private def unlogged : Oracle := ⟨fun _ => some zero, 0, []⟩
/-- Regression: log→cache consistency alone is vacuous on an empty log and
does NOT guarantee its first recorded request was a fresh random-oracle draw. -/
theorem unlogged_coherent : LogConsistent unlogged := by simp [LogConsistent, unlogged]
theorem unlogged_not_complete : ¬CacheLogged unlogged := by
  intro complete
  have impossible := complete [] zero rfl
  simp [unlogged, inputs] at impossible

/- Executed first occurrence is cached for the deliberately incomplete initial
history; the true empty-start control records exactly one fresh and one cached. -/
#guard ((query (fun _ => zero) unlogged [7]).2.log.map (·.fresh)) == [false]
private def repeated : Script Bytes Block Unit 2 :=
  .ask [7] (fun _ => .ask [7] (fun _ => .done ()))
#guard ((run (fun _ => zero) repeated empty).2.log.map (·.fresh)) == [true, false]
#guard (run (fun _ => zero) repeated empty).2.next == 1
private def aborted : Script Bytes Block Unit 1 := .ask [7] (fun _ => .abort)
#guard !(run (fun _ => zero) aborted empty).1.isSome
#guard ((run (fun _ => zero) aborted empty).2.log.map (·.fresh)) == [true]

#print axioms first_fresh_from_empty
#print axioms linked_fresh_order_from_empty
#print axioms query_cache_logged
#print axioms query_flags
#print axioms unlogged_not_complete
end AspisV8Completion.FSFirstFresh
