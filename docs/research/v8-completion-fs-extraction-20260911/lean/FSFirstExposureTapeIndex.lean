import FSFirstFresh
import FSFreshTapeTrace

/-!
# First-exposure events are entries of the one consumed oracle tape

This is the missing deterministic indexing direction between the chronological
first-exposure model and `FSFreshTapeTrace`.  It does not put a probability
law on the tape: it proves that an actual fresh event is one of the exact tape
coordinates already consumed by the execution.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSFirstExposureTapeIndex
open FSOracleExecution FSExposureOrder FSFirstFresh FSFreshTapeTrace

universe u v
variable {I : Type u} {O : Type v} [DecidableEq I]

def freshRank (log : List (Event I O)) (index : Nat) : Nat :=
  (freshAnswers (log.take index)).length

/-- A fresh event occupies exactly the tape coordinate given by the number of
fresh events before it.  Equal answer values at different coordinates do not
blur this chronological identity. -/
theorem fresh_event_has_exact_tape_index (tape : Nat → O) (state : State I O)
    (matched : MatchesTape tape state) (index : Nat)
    (within : index < state.log.length)
    (fresh : (state.log[index]'within).fresh = true) :
    freshRank state.log index < state.next ∧
      (state.log[index]'within).answer = tape (freshRank state.log index) := by
  have takeStep := List.take_succ_eq_append_getElem within
  have freshStep : freshAnswers (state.log.take (index + 1)) =
      freshAnswers (state.log.take index) ++ [(state.log[index]'within).answer] := by
    rw [takeStep]
    unfold freshAnswers
    rw [List.filterMap_append]
    simp [fresh]
  have allSplit : freshAnswers state.log =
      freshAnswers (state.log.take (index + 1)) ++
        freshAnswers (state.log.drop (index + 1)) := by
    have split := (List.take_append_drop (index + 1) state.log).symm
    have mapped := congrArg freshAnswers split
    simpa only [freshAnswers, List.filterMap_append] using mapped
  have prefixBound : freshRank state.log index <
      (freshAnswers (state.log.take (index + 1))).length := by
    rw [freshStep]
    simp [freshRank]
  have wholeBound : freshRank state.log index < (freshAnswers state.log).length := by
    rw [allSplit, List.length_append]
    omega
  have nextLength : (freshAnswers state.log).length = state.next := by
    unfold MatchesTape at matched
    have lengths := congrArg List.length matched
    simpa using lengths
  have rankBefore : freshRank state.log index < state.next := by omega
  have prefixValue :
      (freshAnswers (state.log.take (index + 1)))[freshRank state.log index]? =
        some (state.log[index]'within).answer := by
    rw [freshStep]
    simp [freshRank]
  have wholeValue :
      (freshAnswers state.log)[freshRank state.log index]? =
        some (state.log[index]'within).answer := by
    rw [allSplit, List.getElem?_append_left prefixBound]
    exact prefixValue
  have tapeValue :
      (freshAnswers state.log)[freshRank state.log index]? =
        some (tape (freshRank state.log index)) := by
    rw [matched, List.getElem?_map]
    have rangeAt : (List.range state.next)[freshRank state.log index]? =
        some (freshRank state.log index) := by
      simp [rankBefore]
    rw [rangeAt]
    rfl
  exact ⟨rankBefore, Option.some.inj (wholeValue.symm.trans tapeValue)⟩

/-- Every event marked fresh in a tape-matched history has an actual consumed
tape coordinate.  This is membership in the one tape, not independence of
the event from earlier history. -/
theorem fresh_event_has_tape_index (tape : Nat → O) (state : State I O)
    (matched : MatchesTape tape state) (index : Nat)
    (within : index < state.log.length)
    (fresh : (state.log[index]'within).fresh = true) :
    ∃ coordinate, coordinate < state.next ∧
      (state.log[index]'within).answer = tape coordinate := by
  have answerMember : (state.log[index]'within).answer ∈ freshAnswers state.log := by
    unfold freshAnswers
    apply List.mem_filterMap.mpr
    refine ⟨state.log[index], List.getElem_mem within, ?_⟩
    simp [fresh]
  rw [matched] at answerMember
  obtain ⟨coordinate, coordinateIn, answerEq⟩ := List.mem_map.mp answerMember
  refine ⟨coordinate, ?_, answerEq.symm⟩
  simpa using coordinateIn

/-- Starting from the real empty lazy oracle, the first exposure of every
seen request is fresh and its answer is an actual coordinate of the single
global tape.  The coordinate may depend on the preceding causal history. -/
theorem first_exposure_has_tape_index_from_empty {A : Type} {n : Nat}
    (tape : Nat → Block) (program : Script Bytes Block A n) (input : Bytes)
    (seen : input ∈ inputs (run tape program empty).2.log) :
    ∃ (within : firstExposure (run tape program empty).2.log input <
          (run tape program empty).2.log.length)
      (coordinate : Nat),
      coordinate < (run tape program empty).2.next ∧
      ((run tape program empty).2.log[
        firstExposure (run tape program empty).2.log input]'within).fresh = true ∧
      ((run tape program empty).2.log[
        firstExposure (run tape program empty).2.log input]'within).answer =
          tape coordinate := by
  obtain ⟨within, fresh⟩ := first_fresh_from_empty tape program input seen
  have matched := run_from_empty_matches tape program
  obtain ⟨coordinate, before, answer⟩ :=
    fresh_event_has_tape_index tape _ matched _ within fresh
  exact ⟨within, coordinate, before, fresh, answer⟩

#print axioms fresh_event_has_tape_index
#print axioms fresh_event_has_exact_tape_index
#print axioms first_exposure_has_tape_index_from_empty

end AspisV8Completion.FSFirstExposureTapeIndex
