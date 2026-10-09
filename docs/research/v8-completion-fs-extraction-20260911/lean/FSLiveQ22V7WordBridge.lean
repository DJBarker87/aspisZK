import FSQuerySchedule
import AspisFormal.K1.V7Tag73SamplerDecoder

/-!
# Live q22 query sampling with V7 block-word routing

The selected q22 sampler is not the V7 q16 sampler.  What is reusable without
changing its meaning is the deployed 32-byte-block / eight little-endian-word
decoder.  This file proves that the actual q22 candidate list is precisely
that V7 word list reduced modulo `2^18`, then instruments every live squeeze
of the q22 loop.

Duplicate words, the global 64-draw cap, the detection-block boundary, cache
hits, exhaustion and exact final state are retained.  No uniformity or
freshness claim is made.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSLiveQ22V7WordBridge

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSQuerySampler FSQuerySchedule
open AspisK1.V7Tag73SamplerDecoder

abbrev Tape := FSBoundedTranscript.Tape
abbrev Transcript := FSBoundedTranscript.Transcript
abbrev Block := FSBoundedTranscript.Block

/-- The current q22 source and V7 use exactly the same eight little-endian
u32 words; only the subsequent schedule cardinality differs. -/
theorem queryWords_eq_v7 (block : Block) :
    queryWords block = (blockWords block).map q16Candidate := by
  apply List.ext_getElem
  · simp [query_words_count, blockWords_length]
  · intro index leftBound rightBound
    have bound : index < 8 := by
      simpa [query_words_count] using leftBound
    simp only [queryWords, blockWords, littleEndianWord, q16Candidate, q16Bound,
      List.getElem_map, List.getElem_ofFn, List.getElem_range]
    interval_cases index <;> rfl

structure BlockStep where
  start : Transcript
  output : Block
  final : Transcript
  beforeAccepted : List Nat
  beforeDraws : Nat
  checked : Scan

def blockStep (tape : Tape) (start : Transcript)
    (accepted : List Nat) (draws : Nat) : BlockStep :=
  let squeezed := squeeze tape start
  let checked := scan (queryWords squeezed.1) accepted draws
  ⟨start, squeezed.1, squeezed.2, accepted, draws, checked⟩

structure QueryTrace where
  result : Option (List Nat)
  final : Transcript
  steps : List BlockStep

/-- Exact total instrumentation of `reference`.  Notice that the stop test
occurs after a block is squeezed: the source's detection block is therefore
present in `steps`, including the extra-block boundary case. -/
def queryTrace (tape : Tape) : Nat → Transcript → List Nat → Nat → QueryTrace
  | fuel, start, accepted, draws =>
    if draws < 64 then
      match fuel with
      | 0 => ⟨none, start, []⟩
      | next + 1 =>
        let step := blockStep tape start accepted draws
        if step.checked.stopped then
          ⟨finish step.checked.accepted, step.final, [step]⟩
        else
          let rest := queryTrace tape next step.final
            step.checked.accepted step.checked.draws
          ⟨rest.result, rest.final, step :: rest.steps⟩
    else ⟨finish accepted, start, []⟩

theorem queryTrace_exact (tape : Tape) : ∀ fuel start accepted draws,
    (queryTrace tape fuel start accepted draws).result =
        (reference tape fuel start accepted draws).1 ∧
      (queryTrace tape fuel start accepted draws).final =
        (reference tape fuel start accepted draws).2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro start accepted draws
      by_cases cap : draws < 64 <;>
        simp [queryTrace, reference, cap]
  | succ fuel ih =>
      intro start accepted draws
      by_cases cap : draws < 64
      · simp only [queryTrace, reference, if_pos cap, blockStep]
        by_cases stop :
            (scan (queryWords (squeeze tape start).1) accepted draws).stopped = true
        · simp [stop]
        · simp only [stop, Bool.false_eq_true, if_false]
          simpa using ih (squeeze tape start).2
            (scan (queryWords (squeeze tape start).1) accepted draws).accepted
            (scan (queryWords (squeeze tape start).1) accepted draws).draws
      · simp [queryTrace, reference, cap]

theorem run_queryScript_trace (tape : Tape) (fuel : Nat)
    (start : Transcript) (accepted : List Nat) (draws : Nat) :
    run tape (queryScript fuel start.digest accepted draws) start.oracle =
      (some ((queryTrace tape fuel start accepted draws).result,
        (queryTrace tape fuel start accepted draws).final.digest),
        (queryTrace tape fuel start accepted draws).final.oracle) := by
  rw [run_queries]
  obtain ⟨resultEq, finalEq⟩ :=
    queryTrace_exact tape fuel start accepted draws
  rw [resultEq, finalEq]

inductive ChronologicalSteps (tape : Tape) :
    Transcript → List BlockStep → Transcript → Prop
  | nil (start : Transcript) : ChronologicalSteps tape start [] start
  | cons (start : Transcript) (step : BlockStep)
      (rest : List BlockStep) (final : Transcript)
      (actual : step = blockStep tape start step.beforeAccepted step.beforeDraws)
      (tail : ChronologicalSteps tape step.final rest final) :
      ChronologicalSteps tape start (step :: rest) final

theorem queryTrace_chronological (tape : Tape) : ∀ fuel start accepted draws,
    ChronologicalSteps tape start (queryTrace tape fuel start accepted draws).steps
      (queryTrace tape fuel start accepted draws).final := by
  intro fuel
  induction fuel with
  | zero =>
      intro start accepted draws
      by_cases cap : draws < 64 <;>
        simp [queryTrace, cap, ChronologicalSteps.nil]
  | succ fuel ih =>
      intro start accepted draws
      by_cases cap : draws < 64
      · simp only [queryTrace, if_pos cap]
        let step := blockStep tape start accepted draws
        by_cases stop : step.checked.stopped = true
        · simp only [step, stop, if_true]
          exact .cons start _ [] _ rfl (.nil _)
        · simp only [step, stop, Bool.false_eq_true, if_false]
          exact .cons start _ _ _ rfl
            (ih step.final step.checked.accepted step.checked.draws)
      · simp [queryTrace, cap, ChronologicalSteps.nil]

def V7WordRoutedStep (step : BlockStep) : Prop :=
  queryWords step.output = (blockWords step.output).map q16Candidate

theorem queryTrace_all_steps_v7_words (tape : Tape)
    (fuel : Nat) (start : Transcript) (accepted : List Nat) (draws : Nat) :
    ∀ step ∈ (queryTrace tape fuel start accepted draws).steps,
      V7WordRoutedStep step := by
  intro step member
  exact queryWords_eq_v7 step.output

/-- A successful selected q22 run constructs its typed 22-position schedule
from the same traced blocks.  This uses the q22 invariants, not V7's q16
schedule theorem. -/
theorem successful_queryTrace_schedule (tape : Tape) (start : Transcript)
    (returned : List Nat)
    (success : (queryTrace tape 8 start [] 0).result = some returned) :
    ValidAccepted returned ∧ returned.length = 22 := by
  have exactResult := (queryTrace_exact tape 8 start [] 0).1
  rw [success] at exactResult
  exact reference_success tape 8 start [] returned 0 empty_valid
    exactResult.symm

#print axioms queryWords_eq_v7
#print axioms queryTrace_exact
#print axioms run_queryScript_trace
#print axioms queryTrace_chronological
#print axioms queryTrace_all_steps_v7_words
#print axioms successful_queryTrace_schedule

end AspisV8Completion.FSLiveQ22V7WordBridge
