import FSTranscriptScript

/-! Block-accurate selected q22 query sampler. Source inspected:
crates/aspis-core/src/transcript.rs::challenge_queries_without_replacement,
called with count22, bound2^18, max_draws64.

The source checks completion INSIDE the eight-word loop. A completion on
the last word of a block, before draw64, therefore causes another squeeze
before the inner loop detects success. This extra block is retained here.
The sampler is coupled to the existing full-answer cached squeeze interpreter,
not to 64 independently postulated uniform candidates.

This module proves exact Script/reference state equality. The bounded-loop
fuel adequacy and literal Rust integer/bitwise refinement remain separately
stated obligations; neither is a tiny probability. No uniform law is claimed.
-/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSQuerySampler
open FSOracleExecution FSBoundedTranscript FSTranscriptScript

def queryWords (b : Block) : List Nat := (List.range 8).map fun j =>
  ((b ⟨4*j % 32, Nat.mod_lt _ (by decide)⟩).toNat +
   256 * (b ⟨(4*j+1) % 32, Nat.mod_lt _ (by decide)⟩).toNat +
   65536 * (b ⟨(4*j+2) % 32, Nat.mod_lt _ (by decide)⟩).toNat +
   16777216 * (b ⟨(4*j+3) % 32, Nat.mod_lt _ (by decide)⟩).toNat) % 262144

structure Scan where
  accepted : List Nat
  draws : Nat
  stopped : Bool

def scan : List Nat → List Nat → Nat → Scan
  | [], accepted, draws => ⟨accepted, draws, false⟩
  | word :: rest, accepted, draws =>
    if accepted.length = 22 ∨ draws = 64 then ⟨accepted, draws, true⟩
    else scan rest (if word ∈ accepted then accepted else accepted ++ [word]) (draws+1)

def finish (accepted : List Nat) : Option (List Nat) :=
  if accepted.length = 22 then some accepted else none

/-- Fuel bounds block iterations, not successful challenges or oracle misses.
Each actual squeeze still logs two calls even when they are cached. -/
def reference (tape : Tape) : Nat → Transcript → List Nat → Nat → Option (List Nat) × Transcript
  | fuel, s, accepted, draws =>
    if draws < 64 then
      match fuel with
      | 0 => (none, s)
      | next+1 =>
        let block := squeeze tape s
        let checked := scan (queryWords block.1) accepted draws
        if checked.stopped then (finish checked.accepted, block.2)
        else reference tape next block.2 checked.accepted checked.draws
    else (finish accepted, s)

def queryScript : (fuel : Nat) → Block → List Nat → Nat →
    Script (List UInt8) Block (Option (List Nat) × Block) (2*fuel)
  | fuel, digest, accepted, draws =>
    if draws < 64 then
      match fuel with
      | 0 => .done (none, digest)
      | next+1 =>
        bind (squeezeScript digest) fun block =>
          let checked := scan (queryWords block.1) accepted draws
          if checked.stopped then .done (finish checked.accepted, block.2)
          else queryScript next block.2 checked.accepted checked.draws
    else .done (finish accepted, digest)

theorem run_queries (tape : Tape) (fuel : Nat) (digest : Block) (s : Oracle)
    (accepted : List Nat) (draws : Nat) :
    run tape (queryScript fuel digest accepted draws) s =
      (some ((reference tape fuel ⟨digest,s⟩ accepted draws).1,
        (reference tape fuel ⟨digest,s⟩ accepted draws).2.digest),
        (reference tape fuel ⟨digest,s⟩ accepted draws).2.oracle) := by
  induction fuel generalizing digest s accepted draws with
  | zero =>
    by_cases cap : draws < 64 <;> simp only [queryScript, reference, cap, if_true, if_false, run]
  | succ fuel ih =>
    by_cases cap : draws < 64
    · simp only [queryScript, reference, if_pos cap, run_bind, run_squeeze tape ⟨digest,s⟩]
      by_cases stop : (scan (queryWords (squeeze tape ⟨digest,s⟩).1) accepted draws).stopped = true
      · simp only [stop, Bool.true_eq, if_true, run]
      · simp only [stop, Bool.false_eq_true, if_false]
        exact ih (squeeze tape ⟨digest,s⟩).2.digest (squeeze tape ⟨digest,s⟩).2.oracle
          (scan (queryWords (squeeze tape ⟨digest,s⟩).1) accepted draws).accepted
          (scan (queryWords (squeeze tape ⟨digest,s⟩).1) accepted draws).draws
    · simp only [queryScript, reference, if_neg cap, run]

theorem scan_unstopped_draws (words accepted : List Nat) (draws : Nat)
    (continued : (scan words accepted draws).stopped = false) :
    (scan words accepted draws).draws = draws + words.length := by
  induction words generalizing accepted draws with
  | nil => exact (Nat.add_zero _).symm
  | cons word rest ih =>
    by_cases stop : accepted.length = 22 ∨ draws = 64
    · simp only [scan, if_pos stop, Bool.true_eq_false] at continued
    · simp only [scan, if_neg stop] at continued ⊢
      rw [ih _ _ continued]
      simp only [List.length_cons]
      omega

theorem query_words_count (block : Block) : (queryWords block).length = 8 := by
  simp only [queryWords, List.length_map, List.length_range]

theorem query_words_bounded (block : Block) : ∀ word ∈ queryWords block, word < 262144 := by
  intro word member
  obtain ⟨index, _, equal⟩ := List.mem_map.mp member
  subst word
  exact Nat.mod_lt _ (by decide)

/-- Reachable history for this actual sampler follows from Script execution,
including duplicate candidates, cached squeeze/advance and failed output. -/
theorem queries_valid (tape : Tape) (fuel : Nat) (digest : Block) (s : Oracle)
    (accepted : List Nat) (draws : Nat) (valid : FSFirstFresh.ValidHistory s) :
    FSFirstFresh.ValidHistory (reference tape fuel ⟨digest,s⟩ accepted draws).2.oracle := by
  have produced := FSFirstFresh.run_valid tape (queryScript fuel digest accepted draws) s valid
  rw [run_queries] at produced
  exact produced

#print run_queries
#print axioms run_queries
#print axioms scan_unstopped_draws
#print axioms query_words_bounded
#print axioms queries_valid
end AspisV8Completion.FSQuerySampler
