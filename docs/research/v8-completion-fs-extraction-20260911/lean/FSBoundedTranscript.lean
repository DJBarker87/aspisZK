import FSOracleExecution
set_option autoImplicit false
namespace AspisV8Completion.FSBoundedTranscript
open FSOracleExecution
abbrev Block := Fin 32 → UInt8
abbrev Oracle := State (List UInt8) Block
abbrev Tape := Nat → Block

structure Transcript where
  digest : Block
  oracle : Oracle

def Prefix (a b : Oracle) : Prop := ∃ tail, b.log = a.log ++ tail
theorem prefix_refl (s : Oracle) : Prefix s s := ⟨[], by simp⟩
theorem prefix_trans {a b c : Oracle} (ab : Prefix a b) (bc : Prefix b c) : Prefix a c := by
  obtain ⟨x, hx⟩ := ab
  obtain ⟨y, hy⟩ := bc
  exact ⟨x ++ y, by simp [hy, hx, List.append_assoc]⟩

def absorb (tape : Tape) (s : Transcript) (label : UInt8) (data : List UInt8) : Transcript :=
  let step := query tape s.oracle (List.ofFn s.digest ++ [0, label] ++ data)
  ⟨step.1, step.2⟩

def squeeze (tape : Tape) (s : Transcript) : Block × Transcript :=
  let out := query tape s.oracle (List.ofFn s.digest ++ [1])
  let advance := query tape out.2 (List.ofFn s.digest ++ [2])
  (out.1, ⟨advance.1, advance.2⟩)

theorem query_prefix (tape : Tape) (s : Oracle) (input : List UInt8) :
    Prefix s (query tape s input).2 := by
  obtain ⟨event, h, _, _⟩ := query_log tape s input
  exact ⟨[event], h⟩
theorem absorb_prefix (tape : Tape) (s : Transcript) (label : UInt8) (data : List UInt8) :
    Prefix s.oracle (absorb tape s label data).oracle := query_prefix ..
theorem squeeze_prefix (tape : Tape) (s : Transcript) :
    Prefix s.oracle (squeeze tape s).2.oracle :=
  prefix_trans (query_prefix ..) (query_prefix ..)

/-- Little-endian masked source words: AND (2^31-1) equals this remainder.
No hash-answer projection: the entire Block is retained in Oracle.log. -/
def words (b : Block) : List Nat := (List.range 8).map fun j =>
  ((b ⟨4*j % 32, Nat.mod_lt _ (by decide)⟩).toNat +
   256 * (b ⟨(4*j+1) % 32, Nat.mod_lt _ (by decide)⟩).toNat +
   65536 * (b ⟨(4*j+2) % 32, Nat.mod_lt _ (by decide)⟩).toNat +
   16777216 * (b ⟨(4*j+3) % 32, Nat.mod_lt _ (by decide)⟩).toNat) % 2147483648

structure Stream where
  transcript : Transcript
  remaining : List Nat

def nextWord (tape : Tape) (s : Stream) : Nat × Stream :=
  match s.remaining with
  | x :: tail => (x, ⟨s.transcript, tail⟩)
  | [] =>
      let block := squeeze tape s.transcript
      ((words block.1).head!, ⟨block.2, (words block.1).tail⟩)

theorem nextWord_prefix (tape : Tape) (s : Stream) :
    Prefix s.transcript.oracle (nextWord tape s).2.transcript.oracle := by
  cases h : s.remaining with
  | nil => simpa [nextWord, h] using squeeze_prefix tape s.transcript
  | cons x xs => simpa [nextWord, h] using prefix_refl s.transcript.oracle

/-- Literal bounded per-limb retry shape, preserving the state on exhaustion.
This uses the actual sentinel p, never folds p into zero. -/
def limb (tape : Tape) : Nat → Stream → Option Nat × Stream
  | 0, s => (none, s)
  | n+1, s =>
      let step := nextWord tape s
      if step.1 = 2147483647 then limb tape n step.2 else (some step.1, step.2)

theorem limb_prefix (tape : Tape) : ∀ n s,
    Prefix s.transcript.oracle (limb tape n s).2.transcript.oracle := by
  intro n
  induction n with
  | zero => intro s; exact prefix_refl _
  | succ n ih =>
      intro s
      simp only [limb]
      split
      · exact prefix_trans (nextWord_prefix tape s) (ih _)
      · exact nextWord_prefix tape s

def limbs (tape : Tape) : Nat → Stream → Option (List Nat) × Stream
  | 0, s => (some [], s)
  | n+1, s =>
      let first := limb tape 8 s
      match first.1 with
      | none => (none, first.2)
      | some x =>
          let rest := limbs tape n first.2
          (rest.1.map (x :: ·), rest.2)

theorem limbs_prefix (tape : Tape) : ∀ n s,
    Prefix s.transcript.oracle (limbs tape n s).2.transcript.oracle := by
  intro n
  induction n with
  | zero => intro s; exact prefix_refl _
  | succ n ih =>
      intro s
      simp only [limbs]
      split
      · exact limb_prefix tape 8 s
      · exact prefix_trans (limb_prefix tape 8 s) (ih _)

def challenge (tape : Tape) (s : Transcript) : Option (List Nat) × Transcript :=
  let block := squeeze tape s
  let result := limbs tape 4 ⟨block.2, words block.1⟩
  (result.1, result.2.transcript)

theorem challenge_prefix (tape : Tape) (s : Transcript) :
    Prefix s.oracle (challenge tape s).2.oracle :=
  prefix_trans (squeeze_prefix tape s) (limbs_prefix tape 4 _)

abbrev Root := Fin 26 → UInt8
structure RootCuts where
  c1 : Root
  c2 : Root
  c1Cut : Oracle
  c2Cut : Oracle
  final : Transcript
  lambda : List Nat
  chi : List Nat

/-- No-hash C2-choice control, NOT the general commitment-building adversary.
Use `earlyWithC2` below when C2 construction makes oracle calls.
Selected source order after binding/profile absorption. root1 is already
fixed; root2's legal strategy sees the complete oracle state after lambda/chi.
No completed proof body or future transcript is an input to that strategy.
Abort returns its actual state, not a renormalised successful distribution. -/
def early (tape : Tape) (initial : Transcript) (root1 : Root)
    (chooseC2 : Oracle → List Nat → List Nat → Root) : Option RootCuts × Transcript :=
  let c1 := absorb tape initial 3 (List.ofFn root1)
  let lambda := challenge tape c1
  match lambda.1 with
  | none => (none, lambda.2)
  | some l =>
      let chi := challenge tape lambda.2
      match chi.1 with
      | none => (none, chi.2)
      | some c =>
          let root2 := chooseC2 chi.2.oracle l c
          let final := absorb tape chi.2 9 (List.ofFn root2)
          (some ⟨root1, root2, initial.oracle, chi.2.oracle, final, l, c⟩, final)

/-- Complete causal early-prefix CONSTRUCTOR with a bounded C2 hash program.
Leaf/internal/adversary-first calls made while constructing C2 share the same
cache and log as the transcript. Its cut is AFTER construction, BEFORE root
absorption, not the earlier lambda/chi boundary. Cached calls and aborts remain.
The program selector is fixed across executions; its only dynamic inputs are
the actually available oracle state and two already sampled challenges. -/
def earlyWithC2 {n : Nat} (tape : Tape) (initial : Transcript) (root1 : Root)
    (producer : Oracle → List Nat → List Nat → Script (List UInt8) Block Root n) :
    Option RootCuts × Transcript :=
  let c1 := absorb tape initial 3 (List.ofFn root1)
  let lambda := challenge tape c1
  match lambda.1 with
  | none => (none, lambda.2)
  | some l =>
      let chi := challenge tape lambda.2
      match chi.1 with
      | none => (none, chi.2)
      | some c =>
          let constructed := run tape (producer chi.2.oracle l c) chi.2.oracle
          let beforeAbsorb : Transcript := ⟨chi.2.digest, constructed.2⟩
          match constructed.1 with
          | none => (none, beforeAbsorb)
          | some root2 =>
              let final := absorb tape beforeAbsorb 9 (List.ofFn root2)
              (some ⟨root1, root2, initial.oracle, constructed.2, final, l, c⟩, final)

theorem early_script_cuts {n : Nat} (tape : Tape) (initial : Transcript) (root1 : Root)
    (producer : Oracle → List Nat → List Nat → Script (List UInt8) Block Root n)
    (out : RootCuts) (success : (earlyWithC2 tape initial root1 producer).1 = some out) :
    out.c1Cut = initial.oracle ∧ Prefix out.c1Cut out.c2Cut ∧
      Prefix out.c2Cut out.final.oracle := by
  simp only [earlyWithC2] at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · split at success
      · contradiction
      · cases success
        exact ⟨rfl, prefix_trans (absorb_prefix ..) (prefix_trans (challenge_prefix ..)
          (prefix_trans (challenge_prefix ..) (run_extends ..))), absorb_prefix ..⟩

theorem early_script_abort_prefix {n : Nat} (tape : Tape) (initial : Transcript)
    (root1 : Root)
    (producer : Oracle → List Nat → List Nat → Script (List UInt8) Block Root n) :
    Prefix initial.oracle (earlyWithC2 tape initial root1 producer).2.oracle := by
  simp only [earlyWithC2]
  split
  · exact prefix_trans (absorb_prefix ..) (challenge_prefix ..)
  · split
    · exact prefix_trans (absorb_prefix ..)
        (prefix_trans (challenge_prefix ..) (challenge_prefix ..))
    · split
      · exact prefix_trans (absorb_prefix ..) (prefix_trans (challenge_prefix ..)
          (prefix_trans (challenge_prefix ..) (run_extends ..)))
      · exact prefix_trans (absorb_prefix ..) (prefix_trans (challenge_prefix ..)
          (prefix_trans (challenge_prefix ..)
            (prefix_trans (run_extends ..) (absorb_prefix ..))))

theorem early_script_take {n : Nat} (tape : Tape) (initial : Transcript) (root1 : Root)
    (producer : Oracle → List Nat → List Nat → Script (List UInt8) Block Root n)
    (out : RootCuts) (success : (earlyWithC2 tape initial root1 producer).1 = some out) :
    out.c1Cut.log.length ≤ out.c2Cut.log.length ∧
    out.final.oracle.log.take out.c1Cut.log.length = out.c1Cut.log ∧
    out.final.oracle.log.take out.c2Cut.log.length = out.c2Cut.log := by
  obtain ⟨_, ab, bc⟩ := early_script_cuts tape initial root1 producer out success
  obtain ⟨between, hb⟩ := ab
  obtain ⟨afterCut, ha⟩ := bc
  constructor
  · simp [hb]
  constructor
  · simp [ha, hb, List.append_assoc]
  · simp [ha]

/-- Uniform across CONTINUATIONS of the same post-chi prefix, not a strategy
selected after a completed body. Only at most n unread fresh answers can be
consumed by the bounded builder; cached calls do not consume that interval. -/
theorem c2_builder_continuation_congr {n : Nat} (left right : Tape) (history : Oracle)
    (l c : List Nat)
    (producer : Oracle → List Nat → List Nat → Script (List UInt8) Block Root n)
    (agree : ∀ j, history.next ≤ j → j < history.next + n → left j = right j) :
    run left (producer history l c) history = run right (producer history l c) history :=
  run_tape_congr left right (producer history l c) history agree

/-- Both roots are now results of executed causal hash builders. The initial
shared state includes adversary prequeries; building C1 does not retrospectively
delete them. Transcript digest stays fixed during builder-only oracle calls. -/
def constructBoth {n m : Nat} (tape : Tape) (initial : Transcript)
    (producerC1 : Transcript → Script (List UInt8) Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script (List UInt8) Block Root m) :
    Option RootCuts × Transcript :=
  let c1 := run tape (producerC1 initial) initial.oracle
  let beforeAbsorb : Transcript := ⟨initial.digest, c1.2⟩
  match c1.1 with
  | none => (none, beforeAbsorb)
  | some root1 => earlyWithC2 tape beforeAbsorb root1 producerC2

theorem constructed_cuts {n m : Nat} (tape : Tape) (initial : Transcript)
    (producerC1 : Transcript → Script (List UInt8) Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script (List UInt8) Block Root m)
    (out : RootCuts)
    (success : (constructBoth tape initial producerC1 producerC2).1 = some out) :
    Prefix initial.oracle out.c1Cut ∧ Prefix out.c1Cut out.c2Cut ∧
      Prefix out.c2Cut out.final.oracle := by
  simp only [constructBoth] at success
  split at success
  · contradiction
  · obtain ⟨hc1, h12, h2f⟩ := early_script_cuts tape _ _ producerC2 out success
    exact ⟨by rw [hc1]; exact run_extends .., h12, h2f⟩

theorem constructed_abort_prefix {n m : Nat} (tape : Tape) (initial : Transcript)
    (producerC1 : Transcript → Script (List UInt8) Block Root n)
    (producerC2 : Oracle → List Nat → List Nat → Script (List UInt8) Block Root m) :
    Prefix initial.oracle (constructBoth tape initial producerC1 producerC2).2.oracle := by
  simp only [constructBoth]
  split
  · exact run_extends ..
  · exact prefix_trans (run_extends ..) (early_script_abort_prefix ..)

/-- Source-shaped producer of two CHRONOLOGICAL commitment cuts. Equality of
roots alone, and supplied answer-log inclusion, are not premises. -/
theorem early_cuts (tape : Tape) (initial : Transcript) (root1 : Root)
    (chooseC2 : Oracle → List Nat → List Nat → Root) (out : RootCuts)
    (success : (early tape initial root1 chooseC2).1 = some out) :
    out.c1Cut = initial.oracle ∧ Prefix out.c1Cut out.c2Cut ∧
      Prefix out.c2Cut out.final.oracle := by
  simp only [early] at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · cases success
      exact ⟨rfl, prefix_trans (absorb_prefix ..)
        (prefix_trans (challenge_prefix ..) (challenge_prefix ..)), absorb_prefix ..⟩

/-- Historical answers remain literally present, including repeat/cache calls. -/
theorem early_cut_take (tape : Tape) (initial : Transcript) (root1 : Root)
    (chooseC2 : Oracle → List Nat → List Nat → Root) (out : RootCuts)
    (success : (early tape initial root1 chooseC2).1 = some out) :
    out.final.oracle.log.take out.c1Cut.log.length = out.c1Cut.log ∧
    out.final.oracle.log.take out.c2Cut.log.length = out.c2Cut.log := by
  obtain ⟨_, ab, bc⟩ := early_cuts tape initial root1 chooseC2 out success
  obtain ⟨tail, h⟩ := prefix_trans ab bc
  obtain ⟨tail2, h2⟩ := bc
  constructor
  · simp [h]
  · simp [h2]

/-- Rejected samplers still have constructed chronological histories. -/
theorem early_prefix_even_on_abort (tape : Tape) (initial : Transcript) (root1 : Root)
    (chooseC2 : Oracle → List Nat → List Nat → Root) :
    Prefix initial.oracle (early tape initial root1 chooseC2).2.oracle := by
  simp only [early]
  split
  · exact prefix_trans (absorb_prefix ..) (challenge_prefix ..)
  · split
    · exact prefix_trans (absorb_prefix ..)
        (prefix_trans (challenge_prefix ..) (challenge_prefix ..))
    · exact prefix_trans (absorb_prefix ..) (prefix_trans (challenge_prefix ..)
        (prefix_trans (challenge_prefix ..) (absorb_prefix ..)))

private def zeroBlock : Block := fun _ => 0
private def zeroOracle : Oracle := ⟨fun _ => none, 0, []⟩
private def zeroInitial : Transcript := ⟨zeroBlock, zeroOracle⟩
private def zeroEarly := early (fun _ => zeroBlock) zeroInitial (fun _ => 0)
  (fun _ _ _ _ => 0)

/- Executable nonvacuity: constant full-answer oracle accepts both canonical
zero challenges; exactly two repeated hash calls are retained as cache hits. -/
#guard zeroEarly.1.isSome
#guard zeroEarly.2.oracle.log.length == 6
#guard zeroEarly.2.oracle.next == 4
#guard (zeroEarly.2.oracle.log.map (·.fresh)) == [true, true, true, false, false, true]
#guard (zeroEarly.1.map (fun x => x.c2Cut.log.length)) == some 5

/- All-255 answer bytes reject the first limb eight times. That consumes
one output block, then stops; no second block or C2 root is invented. -/
#guard !(early (fun _ _ => 255) zeroInitial (fun _ => 0) (fun _ _ _ _ => 0)).1.isSome
#guard (early (fun _ _ => 255) zeroInitial (fun _ => 0)
    (fun _ _ _ _ => 0)).2.oracle.log.length == 3

/- C2 leaf-construction call is BEFORE the newly constructed cut, not a late
target hit by fiat. Even an aborting builder preserves its actual call. -/
private def builder (_ : Oracle) (_ _ : List Nat) : Script (List UInt8) Block Root 1 :=
  .ask [99] (fun _ => .done (fun _ => 0))
private def built := earlyWithC2 (fun _ => zeroBlock) zeroInitial (fun _ => 0) builder
#guard built.1.isSome
#guard (built.1.map (fun x => x.c2Cut.log.length)) == some 6
#guard built.2.oracle.log.length == 7
#guard built.2.oracle.next == 5
private def aborted := earlyWithC2 (fun _ => zeroBlock) zeroInitial (fun _ => 0)
  (fun _ _ _ => Script.ask [99] (fun _ => Script.abort (n := 0)))
#guard !aborted.1.isSome
#guard aborted.2.oracle.log.length == 6
private def bothBuilt := constructBoth (fun _ => zeroBlock) zeroInitial
  (fun _ => Script.ask [98] (fun _ => Script.done (fun _ => 0) (n := 0))) builder
#guard bothBuilt.1.isSome
#guard (bothBuilt.1.map (fun x => x.c1Cut.log.length)) == some 1
#guard (bothBuilt.1.map (fun x => x.c2Cut.log.length)) == some 7
#guard bothBuilt.2.oracle.log.length == 8
#guard bothBuilt.2.oracle.next == 6

#print axioms early_cuts
#print axioms early_cut_take
#print axioms challenge_prefix
#print axioms early_prefix_even_on_abort
#print axioms early_script_cuts
#print axioms early_script_abort_prefix
#print axioms early_script_take
#print axioms c2_builder_continuation_congr
#print axioms constructed_cuts
#print axioms constructed_abort_prefix
end AspisV8Completion.FSBoundedTranscript
