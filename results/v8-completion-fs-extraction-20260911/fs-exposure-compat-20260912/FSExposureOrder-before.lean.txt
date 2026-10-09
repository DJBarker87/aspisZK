import FSOracleExecution
set_option autoImplicit false
namespace AspisV8Completion.FSExposureOrder
open FSOracleExecution
abbrev Bytes := List UInt8
abbrev Block := Fin 32 → UInt8
abbrev Log := List (Event Bytes Block)

def blockBytes (b : Block) : Bytes := List.ofFn b
def absorbInput (s : Block) (label : UInt8) (message : Bytes) : Bytes :=
  blockBytes s ++ [0, label] ++ message
def squeezeInput (b : Block) : Bytes := blockBytes b ++ [1]
def inputs (log : Log) : List Bytes := log.map Event.input
def firstExposure (log : Log) (input : Bytes) : Nat := (inputs log).idxOf input

/-- The answer recorded for an actual source absorption. No relationship to
a separately supplied semantic program is presumed. -/
def LinkedAbsorb (log : Log) (input : Bytes) (answer : Block) : Prop :=
  ∃ event ∈ log, event.input = input ∧ event.answer = answer

/-- Extract only actual 33-byte squeeze-query strings ending in source byte 1.
Target cardinality is bounded using DISTINCT earlier input strings; repeat
and restored/cache calls cannot inflate the count of candidate prefixes. -/
def targetOf (input : Bytes) : Option Bytes :=
  if input.length = 33 ∧ input.getLast? = some 1 then some (input.take 32) else none
def priorTargets (log : Log) (cut : Nat) : List Bytes :=
  ((inputs (log.take cut)).eraseDups).filterMap targetOf

theorem targetOf_squeeze (b : Block) : targetOf (squeezeInput b) = some (blockBytes b) := by
  simp [targetOf, squeezeInput, blockBytes]

theorem target_count (log : Log) (cut : Nat) :
    (priorTargets log cut).length ≤ (inputs (log.take cut)).eraseDups.length :=
  List.length_filterMap_le ..

/-- Restoring or appending a verifier replay never creates a new FIRST
exposure of an input that already occurred in the shared history. -/
theorem firstExposure_append_of_seen (log suffix : Log) (input : Bytes)
    (seen : input ∈ inputs log) :
    firstExposure (log ++ suffix) input = firstExposure log input := by
  change input ∈ log.map Event.input at seen
  simp only [firstExposure, inputs, List.map_append, List.idxOf_append, if_pos seen]

/-- Reachable cache/log coherence, rather than an independent log-inclusion
assertion. The empty state has it; actual cached query execution preserves it. -/
def LogConsistent (s : State Bytes Block) : Prop :=
  ∀ event ∈ s.log, s.cache event.input = some event.answer

theorem query_log_consistent (tape : Nat → Block) (s : State Bytes Block) (input : Bytes)
    (consistent : LogConsistent s) : LogConsistent (query tape s input).2 := by
  obtain ⟨newEvent, logeq, inputeq, answereq⟩ := query_log tape s input
  intro event member
  rw [logeq] at member
  rcases List.mem_append.mp member with old | new
  · exact old_answer_preserved tape s input event.input event.answer (consistent event old)
  · have eventeq : event = newEvent := by simpa using new
    subst event
    rw [inputeq, answereq]
    exact answer_installed tape s input

theorem run_log_consistent {A : Type} (tape : Nat → Block) :
    ∀ {n : Nat} (program : Script Bytes Block A n) (s : State Bytes Block),
    LogConsistent s → LogConsistent (run tape program s).2 := by
  intro n program
  induction program with
  | done value => intro s consistent; exact consistent
  | abort => intro s consistent; exact consistent
  | ask input next ih =>
      intro s consistent
      exact ih (query tape s input).1 (query tape s input).2
        (query_log_consistent tape s input consistent)

theorem same_logged_input_same_answer (s : State Bytes Block)
    (consistent : LogConsistent s) (left right : Event Bytes Block)
    (hl : left ∈ s.log) (hr : right ∈ s.log) (same : left.input = right.input) :
    left.answer = right.answer := by
  have l := consistent left hl
  have r := consistent right hr
  rw [same] at l
  exact Option.some.inj (l.symm.trans r)

theorem absorption_not_squeeze (state answer : Block) (label : UInt8) (message : Bytes) :
    absorbInput state label message ≠ squeezeInput answer := by
  intro eq
  have len := congrArg List.length eq
  simp [absorbInput, squeezeInput, blockBytes] at len

theorem seen_of_linked (log : Log) (input : Bytes) (answer : Block)
    (linked : LinkedAbsorb log input answer) : input ∈ inputs log := by
  obtain ⟨event, seen, he, _⟩ := linked
  exact List.mem_map.mpr ⟨event, seen, he⟩

/-- The answer used in the source link is the FIRST absorb exposure's answer,
even when the displayed verifier occurrence was a later cached replay. This
is derived from reachable shared-cache coherence, not assumed separately. -/
theorem first_recorded_answer (s : State Bytes Block) (input : Bytes) (answer : Block)
    (consistent : LogConsistent s) (linked : LinkedAbsorb s.log input answer) :
    ∃ h : firstExposure s.log input < s.log.length,
      (s.log[firstExposure s.log input]'h).input = input ∧
      (s.log[firstExposure s.log input]'h).answer = answer := by
  have seen := seen_of_linked s.log input answer linked
  have within := List.idxOf_lt_length_of_mem seen
  have h : firstExposure s.log input < s.log.length := by
    simpa only [firstExposure, inputs, List.length_map] using within
  have found := List.getElem_idxOf within
  change (inputs s.log)[firstExposure s.log input] = input at found
  simp only [inputs, List.getElem_map] at found
  refine ⟨h, found, ?_⟩
  obtain ⟨actual, actualSeen, actualInput, actualAnswer⟩ := linked
  have same := same_logged_input_same_answer s consistent
    (s.log[firstExposure s.log input]'h) actual (List.getElem_mem h) actualSeen
    (found.trans actualInput.symm)
  exact same.trans actualAnswer

theorem exposure_indices_distinct (log : Log) (a c : Bytes)
    (ha : a ∈ inputs log) (hc : c ∈ inputs log) (different : a ≠ c) :
    firstExposure log a ≠ firstExposure log c := by
  intro eq
  have ea := List.getElem_idxOf (List.idxOf_lt_length_of_mem ha)
  have ec := List.getElem_idxOf (List.idxOf_lt_length_of_mem hc)
  change (inputs log).idxOf a = (inputs log).idxOf c at eq
  have locations := congrArg (fun i => (inputs log)[i]?) eq
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem ha),
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hc), ea, ec] at locations
  apply different
  exact Option.some.inj locations

theorem target_of_earlier_squeeze (log : Log) (answer : Block) (cut : Nat)
    (seen : squeezeInput answer ∈ inputs log)
    (earlier : firstExposure log (squeezeInput answer) < cut) :
    blockBytes answer ∈ priorTargets log cut := by
  have within := List.idxOf_lt_length_of_mem seen
  have before : squeezeInput answer ∈ (inputs log).take cut := by
    apply List.mem_take_iff_getElem.mpr
    exact ⟨firstExposure log (squeezeInput answer), by simp only [firstExposure] at earlier ⊢; omega,
      List.getElem_idxOf within⟩
  have before' : squeezeInput answer ∈ inputs (log.take cut) := by
    simpa [inputs, List.map_take] using before
  apply List.mem_filterMap.mpr
  exact ⟨squeezeInput answer, List.mem_eraseDups.mpr before', targetOf_squeeze answer⟩

/-- First-exposure order, not merely verifier invocation order. Either the
actual source absorption was exposed before its linked squeeze input, OR its
full 256-bit answer is in the finite set extracted from the actual earlier
log at the absorption's FIRST exposure. No supplied history subset is used. -/
theorem linked_order_or_premature_target (log : Log) (state answer : Block)
    (label : UInt8) (message : Bytes)
    (linked : LinkedAbsorb log (absorbInput state label message) answer)
    (squeezed : squeezeInput answer ∈ inputs log) :
    firstExposure log (absorbInput state label message) <
      firstExposure log (squeezeInput answer) ∨
    blockBytes answer ∈ priorTargets log
      (firstExposure log (absorbInput state label message)) := by
  have distinct := exposure_indices_distinct log _ _ (seen_of_linked log _ _ linked)
    squeezed (absorption_not_squeeze state answer label message)
  by_cases ordered : firstExposure log (absorbInput state label message) <
      firstExposure log (squeezeInput answer)
  · exact Or.inl ordered
  · exact Or.inr (target_of_earlier_squeeze log answer _ squeezed (by omega))

/- Nonvacuity/regressions are exact executable finite histories, not estimates
of random-oracle failure frequency or evidence of an accepting payment forgery. -/
private def zero : Block := fun _ => 0
private def sourceInput := absorbInput zero 3 [5]
private def normal : Log := [⟨sourceInput, zero, true⟩, ⟨squeezeInput zero, zero, true⟩]
private def premature : Log := [⟨squeezeInput zero, zero, true⟩,
  ⟨sourceInput, zero, true⟩, ⟨squeezeInput zero, zero, false⟩]
#guard firstExposure normal sourceInput == 0
#guard firstExposure normal (squeezeInput zero) == 1
#guard firstExposure premature sourceInput == 1
#guard firstExposure premature (squeezeInput zero) == 0
#guard (priorTargets premature 1).contains (blockBytes zero)
#guard (priorTargets premature 3).length == 1
#guard firstExposure (premature ++ normal) sourceInput == 1
#guard firstExposure (premature ++ normal) (squeezeInput zero) == 0

#print axioms linked_order_or_premature_target
#print axioms target_count
#print axioms firstExposure_append_of_seen
#print axioms run_log_consistent
#print axioms same_logged_input_same_answer
#print axioms first_recorded_answer
end AspisV8Completion.FSExposureOrder
