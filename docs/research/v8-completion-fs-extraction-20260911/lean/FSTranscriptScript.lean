import FSBoundedTranscript
import FSFirstFresh
set_option autoImplicit false
namespace AspisV8Completion.FSTranscriptScript
open FSOracleExecution FSBoundedTranscript
variable {A B : Type}

/-- Increasing a static call allowance never performs a dummy oracle call. -/
def promote : {n : Nat} → Script (List UInt8) Block A n → Script (List UInt8) Block A (n+1)
  | _, .done a => .done a
  | _, .abort => .abort
  | _, .ask input next => .ask input (fun answer => promote (next answer))

theorem run_promote (tape : Tape) : ∀ {n : Nat} (p : Script (List UInt8) Block A n) (s : Oracle),
    run tape (promote p) s = run tape p s := by
  intro n p
  induction p with
  | done a => intro s; rfl
  | abort => intro s; rfl
  | ask input next ih => intro s; exact ih (query tape s input).1 (query tape s input).2

def pad {n : Nat} (p : Script (List UInt8) Block A n) :
    (extra : Nat) → Script (List UInt8) Block A (n+extra)
  | 0 => p
  | extra+1 => promote (pad p extra)

theorem run_pad (tape : Tape) {n : Nat} (p : Script (List UInt8) Block A n)
    (s : Oracle) (extra : Nat) : run tape (pad p extra) s = run tape p s := by
  induction extra with
  | zero => rfl
  | succ extra ih => simpa only [pad, run_promote] using ih

/-- Sequential causal composition with summed worst-case budget. An abort of
the first program retains its actual final oracle and never calls next. -/
def bind {m : Nat} : {n : Nat} → Script (List UInt8) Block A n →
    (A → Script (List UInt8) Block B m) → Script (List UInt8) Block B (m+n)
  | n, .done a, next => pad (next a) n
  | _, .abort, _ => .abort
  | _, .ask input response, next => .ask input (fun answer => bind (response answer) next)

theorem run_bind (tape : Tape) {m : Nat} : ∀ {n : Nat}
    (p : Script (List UInt8) Block A n) (next : A → Script (List UInt8) Block B m) (s : Oracle),
    run tape (bind p next) s =
      match (run tape p s).1 with
      | none => (none, (run tape p s).2)
      | some a => run tape (next a) (run tape p s).2 := by
  intro n p
  induction p with
  | done a => intro next s; simp only [bind, run_pad, run]
  | abort => intro next s; rfl
  | ask input response ih =>
      intro next s
      exact ih (query tape s input).1 next (query tape s input).2

def map {n : Nat} (f : A → B) : Script (List UInt8) Block A n → Script (List UInt8) Block B n
  | .done a => .done (f a)
  | .abort => .abort
  | .ask input next => .ask input (fun answer => map f (next answer))

theorem run_map (tape : Tape) {n : Nat} (f : A → B) (p : Script (List UInt8) Block A n)
    (s : Oracle) : run tape (map f p) s = ((run tape p s).1.map f, (run tape p s).2) := by
  induction p generalizing s with
  | done a => rfl
  | abort => rfl
  | ask input next ih => exact ih (query tape s input).1 (query tape s input).2

def absorbScript (digest : Block) (label : UInt8) (data : List UInt8) :
    Script (List UInt8) Block Block 1 :=
  .ask (List.ofFn digest ++ [0,label] ++ data) (fun answer => .done answer)

def squeezeScript (digest : Block) : Script (List UInt8) Block (Block × Block) 2 :=
  .ask (List.ofFn digest ++ [1]) (fun answer =>
    .ask (List.ofFn digest ++ [2]) (fun advanced => .done (answer, advanced)))

theorem run_absorb (tape : Tape) (s : Transcript) (label : UInt8) (data : List UInt8) :
    run tape (absorbScript s.digest label data) s.oracle =
      (some (absorb tape s label data).digest, (absorb tape s label data).oracle) := rfl

theorem run_squeeze (tape : Tape) (s : Transcript) :
    run tape (squeezeScript s.digest) s.oracle =
      (some ((squeeze tape s).1, (squeeze tape s).2.digest), (squeeze tape s).2.oracle) := rfl

abbrev LocalStream := Block × List Nat
def projectStream (s : Stream) : LocalStream := (s.transcript.digest, s.remaining)
def wordScript (digest : Block) (remaining : List Nat) :
    Script (List UInt8) Block (Nat × LocalStream) 2 :=
  match remaining with
  | x :: tail => .done (x, digest, tail)
  | [] => map (fun pair => ((words pair.1).head!, pair.2, (words pair.1).tail)) (squeezeScript digest)

theorem run_word (tape : Tape) (s : Stream) :
    run tape (wordScript s.transcript.digest s.remaining) s.transcript.oracle =
      (some ((nextWord tape s).1, projectStream (nextWord tape s).2),
        (nextWord tape s).2.transcript.oracle) := by
  cases h : s.remaining with
  | nil => simp only [wordScript, h, run_map, run_squeeze, nextWord, projectStream]; rfl
  | cons x tail => simp only [wordScript, h, run, nextWord, projectStream]

def limbScript : (tries : Nat) → Block → List Nat →
    Script (List UInt8) Block (Option Nat × LocalStream) (2*tries)
  | 0, digest, remaining => .done (none, digest, remaining)
  | tries+1, digest, remaining =>
      bind (wordScript digest remaining) fun step =>
        if step.1 = 2147483647 then limbScript tries step.2.1 step.2.2
        else .done (some step.1, step.2)

theorem run_limb (tape : Tape) : ∀ tries (s : Stream),
    run tape (limbScript tries s.transcript.digest s.remaining) s.transcript.oracle =
      (some ((limb tape tries s).1, projectStream (limb tape tries s).2),
        (limb tape tries s).2.transcript.oracle) := by
  intro tries
  induction tries with
  | zero => intro s; rfl
  | succ tries ih =>
      intro s
      simp only [limbScript, run_bind, run_word]
      simp only [limb]
      split
      · exact ih (nextWord tape s).2
      · rfl

def limbsScript : (count : Nat) → Block → List Nat →
    Script (List UInt8) Block (Option (List Nat) × LocalStream) (16*count)
  | 0, digest, remaining => .done (some [], digest, remaining)
  | count+1, digest, remaining =>
      bind (limbScript 8 digest remaining) fun step =>
        match step.1 with
        | none => .done (none, step.2)
        | some x => map (fun rest => (rest.1.map (x :: ·), rest.2))
            (limbsScript count step.2.1 step.2.2)

theorem run_limbs (tape : Tape) : ∀ count (s : Stream),
    run tape (limbsScript count s.transcript.digest s.remaining) s.transcript.oracle =
      (some ((limbs tape count s).1, projectStream (limbs tape count s).2),
        (limbs tape count s).2.transcript.oracle) := by
  intro count
  induction count with
  | zero => intro s; rfl
  | succ count ih =>
      intro s
      simp only [limbsScript, run_bind, run_limb, limbs]
      cases h : (limb tape 8 s).1 with
      | none => simp only [run]
      | some x =>
        simp only [run_map, projectStream]
        rw [ih (limb tape 8 s).2]
        rfl

def challengeScript (digest : Block) :
    Script (List UInt8) Block (Option (List Nat) × Block) 66 :=
  bind (squeezeScript digest) fun block =>
    map (fun result => (result.1, result.2.1)) (limbsScript 4 block.2 (words block.1))

/-- Exact result, digest, cache, fresh-tape index and complete log equality for
ARBITRARY initial oracle/tape. Sampler failure is returned as inner none with
the actual consumed state, not silently discarded or normalised away.
66 is a conservative call allowance, not a claim the source makes 66 calls. -/
theorem run_challenge (tape : Tape) (s : Transcript) :
    run tape (challengeScript s.digest) s.oracle =
      (some ((challenge tape s).1, (challenge tape s).2.digest), (challenge tape s).2.oracle) := by
  simp only [challengeScript, run_bind, run_squeeze, run_map]
  rw [run_limbs tape 4 ⟨(squeeze tape s).2, words (squeeze tape s).1⟩]
  rfl

theorem absorb_valid (tape : Tape) (s : Transcript) (label : UInt8) (data : List UInt8)
    (valid : FSFirstFresh.ValidHistory s.oracle) :
    FSFirstFresh.ValidHistory (absorb tape s label data).oracle := by
  have derived := FSFirstFresh.run_valid tape (absorbScript s.digest label data) s.oracle valid
  simpa only [run_absorb] using derived

theorem squeeze_valid (tape : Tape) (s : Transcript)
    (valid : FSFirstFresh.ValidHistory s.oracle) :
    FSFirstFresh.ValidHistory (squeeze tape s).2.oracle := by
  have derived := FSFirstFresh.run_valid tape (squeezeScript s.digest) s.oracle valid
  simpa only [run_squeeze] using derived

theorem challenge_valid (tape : Tape) (s : Transcript)
    (valid : FSFirstFresh.ValidHistory s.oracle) :
    FSFirstFresh.ValidHistory (challenge tape s).2.oracle := by
  have derived := FSFirstFresh.run_valid tape (challengeScript s.digest) s.oracle valid
  simpa only [run_challenge] using derived

theorem challenge_call_allowance (tape : Tape) (s : Transcript) :
    (challenge tape s).2.oracle.log.length ≤ s.oracle.log.length + 66 := by
  have bound := FSOracleExecution.call_bound tape (challengeScript s.digest) s.oracle
  simpa only [run_challenge] using bound

theorem earlyWithC2_valid {n : Nat} (tape : Tape) (initial : Transcript) (root1 : Root)
    (producer : Oracle → List Nat → List Nat → Script (List UInt8) Block Root n)
    (valid : FSFirstFresh.ValidHistory initial.oracle) :
    FSFirstFresh.ValidHistory (earlyWithC2 tape initial root1 producer).2.oracle := by
  have vc1 := absorb_valid tape initial 3 (List.ofFn root1) valid
  have vl := challenge_valid tape _ vc1
  have vc := challenge_valid tape _ vl
  simp only [earlyWithC2]
  split
  · exact vl
  · split
    · exact vc
    · split
      · exact FSFirstFresh.run_valid tape _ _ vc
      · exact absorb_valid tape _ _ _ (FSFirstFresh.run_valid tape _ _ vc)

theorem constructBoth_valid {n m : Nat} (tape : Tape) (initial : Transcript)
    (producerC1 : Transcript → Script (List UInt8) Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script (List UInt8) Block Root m)
    (valid : FSFirstFresh.ValidHistory initial.oracle) :
    FSFirstFresh.ValidHistory (constructBoth tape initial producerC1 producerC2).2.oracle := by
  have vc1 := FSFirstFresh.run_valid tape (producerC1 initial) initial.oracle valid
  simp only [constructBoth]
  split
  · exact vc1
  · exact earlyWithC2_valid tape _ _ _ vc1

/-- The actual source-shaped two-commitment path now CONSTRUCTS complete
chronological history from empty. No successful-result, coherence, freshness,
sampler success or source/script correspondence predicate is a caller premise. -/
theorem constructBoth_valid_from_empty {n m : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script (List UInt8) Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script (List UInt8) Block Root m) :
    FSFirstFresh.ValidHistory
      (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).2.oracle :=
  constructBoth_valid tape _ _ _ FSFirstFresh.empty_valid

theorem constructBoth_first_fresh {n m : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript → Script (List UInt8) Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script (List UInt8) Block Root m)
    (input : List UInt8)
    (seen : input ∈ FSExposureOrder.inputs
      (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).2.oracle.log) :
    ∃ h : FSExposureOrder.firstExposure
        (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).2.oracle.log input <
        (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).2.oracle.log.length,
      ((constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).2.oracle.log[
        FSExposureOrder.firstExposure
          (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).2.oracle.log input]'h).fresh = true :=
  FSFirstFresh.first_fresh _ (constructBoth_valid_from_empty tape digest producerC1 producerC2) input seen

private def zero : Block := fun _ => 0
private def all255 : Block := fun _ => 255
/- Exact deterministic controls. Outer some records that the bounded script
ran; inner none is the retained source sampler rejection, never success. -/
#guard (run (fun _ => zero) (challengeScript zero) FSFirstFresh.empty).1.isSome
#guard ((run (fun _ => zero) (challengeScript zero) FSFirstFresh.empty).1.map
  (fun result => result.1)) == some (some [0,0,0,0])
#guard ((run (fun _ => all255) (challengeScript zero) FSFirstFresh.empty).1.map
  (fun result => result.1)) == some none
#guard (run (fun _ => all255) (challengeScript zero) FSFirstFresh.empty).2.log.length == 2

#print axioms run_absorb
#print axioms run_squeeze
#print axioms run_challenge
#print axioms constructBoth_valid_from_empty
#print axioms constructBoth_first_fresh
#print axioms challenge_call_allowance
end AspisV8Completion.FSTranscriptScript
