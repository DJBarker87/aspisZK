import FSBoundedTranscript

/-!
# Instrumented live challenge block trace

This file records precisely the blocks produced when the existing lazy
`FSBoundedTranscript` word stream calls `squeeze`.  Erasing the trace is proved
equal to the existing execution on successes, failures, cache hits, and early
stops.  It makes no freshness or probability claim.
-/

set_option autoImplicit false

namespace AspisV8Completion.FSLiveChallengeTrace
open FSBoundedTranscript

structure TraceStream where
  current : Stream
  blocks : List Block
  draws : Nat
  drawn : List Nat

def erase (s : TraceStream) : Stream := s.current

/-- A chronological path of actual `squeeze` calls.  The relation uses the
same tape, digest and oracle state as the source model, so cached calls and
their unchanged tape cursor are retained rather than idealised away. -/
inductive SqueezePath (tape : Tape) : Transcript → List Block → Transcript → Prop
  | nil (start : Transcript) : SqueezePath tape start [] start
  | snoc {start current : Transcript} {blocks : List Block}
      (path : SqueezePath tape start blocks current) :
      SqueezePath tape start (blocks ++ [(squeeze tape current).1])
        (squeeze tape current).2

def nextWord (tape : Tape) (s : TraceStream) : Nat × TraceStream :=
  match s.current.remaining with
  | x :: tail =>
      (x, ⟨⟨s.current.transcript, tail⟩, s.blocks, s.draws + 1,
        s.drawn ++ [x]⟩)
  | [] =>
      let block := squeeze tape s.current.transcript
      ((words block.1).head!,
        ⟨⟨block.2, (words block.1).tail⟩,
          s.blocks ++ [block.1], s.draws + 1,
          s.drawn ++ [(words block.1).head!]⟩)

theorem nextWord_erase (tape : Tape) (s : TraceStream) :
    (nextWord tape s).1 = (FSBoundedTranscript.nextWord tape (erase s)).1 ∧
      erase (nextWord tape s).2 =
        (FSBoundedTranscript.nextWord tape (erase s)).2 := by
  cases h : s.current.remaining with
  | nil => simp [nextWord, erase, FSBoundedTranscript.nextWord, h]
  | cons x tail => simp [nextWord, erase, FSBoundedTranscript.nextWord, h]

theorem nextWord_path (tape : Tape) (start : Transcript) (s : TraceStream)
    (path : SqueezePath tape start s.blocks s.current.transcript) :
    SqueezePath tape start (nextWord tape s).2.blocks
      (nextWord tape s).2.current.transcript := by
  cases h : s.current.remaining with
  | nil =>
      simpa [nextWord, h] using SqueezePath.snoc path
  | cons x tail => simpa [nextWord, h] using path

def Balanced (s : TraceStream) : Prop :=
  8 * s.blocks.length = s.draws + s.current.remaining.length

def Content (s : TraceStream) : Prop :=
  s.blocks.flatMap words = s.drawn ++ s.current.remaining

def DrawCount (s : TraceStream) : Prop := s.drawn.length = s.draws

def Canonical (s : TraceStream) : Prop :=
  ∀ word ∈ s.current.remaining, word < 2147483648

theorem words_length (block : Block) : (words block).length = 8 := by
  simp [words]

theorem words_canonical (block : Block) (word : Nat)
    (member : word ∈ words block) : word < 2147483648 := by
  simp only [words, List.mem_map] at member
  obtain ⟨index, _, rfl⟩ := member
  exact Nat.mod_lt _ (by decide)

theorem nextWord_draws (tape : Tape) (s : TraceStream) :
    (nextWord tape s).2.draws = s.draws + 1 := by
  cases h : s.current.remaining <;> simp [nextWord, h]

theorem nextWord_drawn (tape : Tape) (s : TraceStream) :
    (nextWord tape s).2.drawn = s.drawn ++ [(nextWord tape s).1] := by
  cases h : s.current.remaining <;> simp [nextWord, h]

theorem nextWord_value_lt (tape : Tape) (s : TraceStream)
    (canonical : Canonical s) : (nextWord tape s).1 < 2147483648 := by
  cases h : s.current.remaining with
  | nil =>
      simp only [nextWord, h]
      apply words_canonical
      cases hw : words (squeeze tape s.current.transcript).1 with
      | nil =>
          have len := words_length (squeeze tape s.current.transcript).1
          rw [hw] at len
          contradiction
      | cons word tail =>
          change (word :: tail).head! ∈ word :: tail
          exact List.mem_cons_self
  | cons word tail =>
      simp only [nextWord, h]
      exact canonical word (by simp [h])

theorem nextWord_canonical (tape : Tape) (s : TraceStream)
    (canonical : Canonical s) : Canonical (nextWord tape s).2 := by
  intro word member
  cases h : s.current.remaining with
  | nil =>
      simp only [nextWord, h] at member
      exact words_canonical _ word (List.mem_of_mem_tail member)
  | cons head tail =>
      simp only [nextWord, h] at member
      exact canonical word (by simp [h, member])

theorem nextWord_content (tape : Tape) (s : TraceStream)
    (content : Content s) : Content (nextWord tape s).2 := by
  rcases s with ⟨⟨transcript, remaining⟩, blocks, draws, drawn⟩
  cases h : remaining with
  | nil =>
      subst remaining
      simp only [Content, List.append_nil] at content
      cases hw : words (squeeze tape transcript).1 with
      | nil =>
          have len := words_length (squeeze tape transcript).1
          rw [hw] at len
          contradiction
      | cons word tail =>
          simp [nextWord, hw, Content, content, List.append_assoc]
          rfl
  | cons word tail =>
      subst remaining
      simp only [Content] at content
      simp [nextWord, Content, content, List.append_assoc]

theorem nextWord_drawCount (tape : Tape) (s : TraceStream)
    (count : DrawCount s) : DrawCount (nextWord tape s).2 := by
  change s.drawn.length = s.draws at count
  change (nextWord tape s).2.drawn.length = (nextWord tape s).2.draws
  cases h : s.current.remaining <;>
    simp [nextWord, h, count]

theorem nextWord_balanced (tape : Tape) (s : TraceStream)
    (balanced : Balanced s) : Balanced (nextWord tape s).2 := by
  rcases s with ⟨⟨transcript, remaining⟩, blocks, draws, drawn⟩
  cases h : remaining with
  | nil =>
      subst remaining
      have len := words_length (squeeze tape transcript).1
      simp only [nextWord, Balanced, List.length_append,
        List.length_singleton, List.length_tail]
      simp only [Balanced, List.length_nil, Nat.add_zero] at balanced
      rw [len]
      omega
  | cons x tail =>
      subst remaining
      simp only [nextWord, Balanced, List.length_cons] at balanced ⊢
      omega

theorem nextWord_remaining_le (tape : Tape) (s : TraceStream)
    (bound : s.current.remaining.length ≤ 8) :
    (nextWord tape s).2.current.remaining.length ≤ 8 := by
  rcases s with ⟨⟨transcript, remaining⟩, blocks, draws, drawn⟩
  cases h : remaining with
  | nil =>
      have len := words_length (squeeze tape transcript).1
      simp only [nextWord, h, List.length_tail]
      omega
  | cons x tail =>
      simp only [nextWord, h, List.length_cons] at bound
      simp only [nextWord, h]
      omega

theorem nextWord_remaining_lt (tape : Tape) (s : TraceStream)
    (bound : s.current.remaining.length ≤ 8) :
    (nextWord tape s).2.current.remaining.length < 8 := by
  rcases s with ⟨⟨transcript, remaining⟩, blocks, draws, drawn⟩
  cases h : remaining with
  | nil =>
      have len := words_length (squeeze tape transcript).1
      simp only [nextWord, h, List.length_tail]
      omega
  | cons x tail =>
      simp only [nextWord, h, List.length_cons] at bound
      simp only [nextWord, h]
      omega

def limb (tape : Tape) : Nat → TraceStream → Option Nat × TraceStream
  | 0, s => (none, s)
  | n+1, s =>
      let step := nextWord tape s
      if step.1 = 2147483647 then limb tape n step.2
      else (some step.1, step.2)

theorem limb_erase (tape : Tape) : ∀ n s,
    (limb tape n s).1 =
        (FSBoundedTranscript.limb tape n (erase s)).1 ∧
      erase (limb tape n s).2 =
        (FSBoundedTranscript.limb tape n (erase s)).2 := by
  intro n
  induction n with
  | zero => intro s; exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro s
      simp only [limb, FSBoundedTranscript.limb]
      obtain ⟨valueEq, streamEq⟩ := nextWord_erase tape s
      rw [← valueEq]
      split
      · simpa [streamEq] using ih (nextWord tape s).2
      · exact ⟨rfl, streamEq⟩

theorem limb_path (tape : Tape) (start : Transcript) : ∀ n s,
    SqueezePath tape start s.blocks s.current.transcript →
      SqueezePath tape start (limb tape n s).2.blocks
        (limb tape n s).2.current.transcript := by
  intro n
  induction n with
  | zero => intro s path; exact path
  | succ n ih =>
      intro s path
      simp only [limb]
      split
      · exact ih _ (nextWord_path tape start s path)
      · exact nextWord_path tape start s path

theorem limb_content (tape : Tape) : ∀ n s, Content s →
    Content (limb tape n s).2 := by
  intro n
  induction n with
  | zero => intro s content; exact content
  | succ n ih =>
      intro s content
      simp only [limb]
      split
      · exact ih _ (nextWord_content tape s content)
      · exact nextWord_content tape s content

theorem limb_drawCount (tape : Tape) : ∀ n s, DrawCount s →
    DrawCount (limb tape n s).2 := by
  intro n
  induction n with
  | zero => intro s count; exact count
  | succ n ih =>
      intro s count
      simp only [limb]
      split
      · exact ih _ (nextWord_drawCount tape s count)
      · exact nextWord_drawCount tape s count

theorem limb_drawn_prefix (tape : Tape) : ∀ n s,
    s.drawn <+: (limb tape n s).2.drawn := by
  intro n
  induction n with
  | zero => intro s; exact List.prefix_refl _
  | succ n ih =>
      intro s
      simp only [limb]
      split
      · exact (List.prefix_append s.drawn [(nextWord tape s).1]).trans
          (by simpa [nextWord_drawn] using ih (nextWord tape s).2)
      · change s.drawn <+: (nextWord tape s).2.drawn
        rw [nextWord_drawn]
        exact List.prefix_append _ _

theorem limb_canonical (tape : Tape) : ∀ n s, Canonical s →
    Canonical (limb tape n s).2 := by
  intro n
  induction n with
  | zero => intro s canonical; exact canonical
  | succ n ih =>
      intro s canonical
      simp only [limb]
      split
      · exact ih _ (nextWord_canonical tape s canonical)
      · exact nextWord_canonical tape s canonical

theorem limb_balanced (tape : Tape) : ∀ n s, Balanced s →
    Balanced (limb tape n s).2 := by
  intro n
  induction n with
  | zero => intro s balanced; exact balanced
  | succ n ih =>
      intro s balanced
      simp only [limb]
      split
      · exact ih _ (nextWord_balanced tape s balanced)
      · exact nextWord_balanced tape s balanced

theorem limb_remaining_le (tape : Tape) : ∀ n s,
    s.current.remaining.length ≤ 8 →
      (limb tape n s).2.current.remaining.length ≤ 8 := by
  intro n
  induction n with
  | zero => intro s bound; exact bound
  | succ n ih =>
      intro s bound
      simp only [limb]
      split
      · exact ih _ (nextWord_remaining_le tape s bound)
      · exact nextWord_remaining_le tape s bound

theorem limb_remaining_lt (tape : Tape) : ∀ n s,
    s.current.remaining.length < 8 →
      (limb tape n s).2.current.remaining.length < 8 := by
  intro n
  induction n with
  | zero => intro s bound; exact bound
  | succ n ih =>
      intro s bound
      simp only [limb]
      split
      · exact ih _ (nextWord_remaining_lt tape s (Nat.le_of_lt bound))
      · exact nextWord_remaining_lt tape s (Nat.le_of_lt bound)

theorem limb_succ_remaining_lt (tape : Tape) (n : Nat) (s : TraceStream)
    (bound : s.current.remaining.length ≤ 8) :
    (limb tape (n+1) s).2.current.remaining.length < 8 := by
  simp only [limb]
  split
  · exact limb_remaining_lt tape n _ (nextWord_remaining_lt tape s bound)
  · exact nextWord_remaining_lt tape s bound

theorem limb_draws_le (tape : Tape) : ∀ n s,
    (limb tape n s).2.draws ≤ s.draws + n := by
  intro n
  induction n with
  | zero => intro s; simp [limb]
  | succ n ih =>
      intro s
      simp only [limb]
      split
      · have tail := ih (nextWord tape s).2
        rw [nextWord_draws] at tail
        omega
      · rw [nextWord_draws]
        omega

theorem limb_draws_mono (tape : Tape) : ∀ n s,
    s.draws ≤ (limb tape n s).2.draws := by
  intro n
  induction n with
  | zero => intro s; exact Nat.le_refl _
  | succ n ih =>
      intro s
      simp only [limb]
      split
      · exact Nat.le_trans (by rw [nextWord_draws]; omega) (ih _)
      · rw [nextWord_draws]
        omega

theorem limb_succ_draws_lt (tape : Tape) (n : Nat) (s : TraceStream) :
    s.draws < (limb tape (n+1) s).2.draws := by
  simp only [limb]
  split
  · have mono := limb_draws_mono tape n (nextWord tape s).2
    rw [nextWord_draws] at mono
    omega
  · rw [nextWord_draws]
    omega

def limbs (tape : Tape) : Nat → TraceStream → Option (List Nat) × TraceStream
  | 0, s => (some [], s)
  | n+1, s =>
      let first := limb tape 8 s
      match first.1 with
      | none => (none, first.2)
      | some x =>
          let rest := limbs tape n first.2
          (rest.1.map (x :: ·), rest.2)

theorem limbs_erase (tape : Tape) : ∀ n s,
    (limbs tape n s).1 =
        (FSBoundedTranscript.limbs tape n (erase s)).1 ∧
      erase (limbs tape n s).2 =
        (FSBoundedTranscript.limbs tape n (erase s)).2 := by
  intro n
  induction n with
  | zero => intro s; exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro s
      simp only [limbs, FSBoundedTranscript.limbs]
      obtain ⟨valueEq, streamEq⟩ := limb_erase tape 8 s
      rw [← valueEq]
      cases result : (limb tape 8 s).1 with
      | none => exact ⟨rfl, streamEq⟩
      | some value =>
          obtain ⟨tailEq, tailStreamEq⟩ := ih (limb tape 8 s).2
          rw [← streamEq]
          exact ⟨congrArg (Option.map (value :: ·)) tailEq, tailStreamEq⟩

theorem limbs_path (tape : Tape) (start : Transcript) : ∀ n s,
    SqueezePath tape start s.blocks s.current.transcript →
      SqueezePath tape start (limbs tape n s).2.blocks
        (limbs tape n s).2.current.transcript := by
  intro n
  induction n with
  | zero => intro s path; exact path
  | succ n ih =>
      intro s path
      simp only [limbs]
      cases result : (limb tape 8 s).1 with
      | none => exact limb_path tape start 8 s path
      | some value => exact ih _ (limb_path tape start 8 s path)

theorem limbs_content (tape : Tape) : ∀ n s, Content s →
    Content (limbs tape n s).2 := by
  intro n
  induction n with
  | zero => intro s content; exact content
  | succ n ih =>
      intro s content
      simp only [limbs]
      cases result : (limb tape 8 s).1 with
      | none => exact limb_content tape 8 s content
      | some value => exact ih _ (limb_content tape 8 s content)

theorem limbs_drawCount (tape : Tape) : ∀ n s, DrawCount s →
    DrawCount (limbs tape n s).2 := by
  intro n
  induction n with
  | zero => intro s count; exact count
  | succ n ih =>
      intro s count
      simp only [limbs]
      cases result : (limb tape 8 s).1 with
      | none => exact limb_drawCount tape 8 s count
      | some value => exact ih _ (limb_drawCount tape 8 s count)

theorem limbs_drawn_prefix (tape : Tape) : ∀ n s,
    s.drawn <+: (limbs tape n s).2.drawn := by
  intro n
  induction n with
  | zero => intro s; exact List.prefix_refl _
  | succ n ih =>
      intro s
      simp only [limbs]
      cases result : (limb tape 8 s).1 with
      | none => exact limb_drawn_prefix tape 8 s
      | some value =>
          exact (limb_drawn_prefix tape 8 s).trans (ih _)

theorem limbs_balanced (tape : Tape) : ∀ n s, Balanced s →
    Balanced (limbs tape n s).2 := by
  intro n
  induction n with
  | zero => intro s balanced; exact balanced
  | succ n ih =>
      intro s balanced
      simp only [limbs]
      cases result : (limb tape 8 s).1 with
      | none => exact limb_balanced tape 8 s balanced
      | some value => exact ih _ (limb_balanced tape 8 s balanced)

theorem limbs_remaining_le (tape : Tape) : ∀ n s,
    s.current.remaining.length ≤ 8 →
      (limbs tape n s).2.current.remaining.length ≤ 8 := by
  intro n
  induction n with
  | zero => intro s bound; exact bound
  | succ n ih =>
      intro s bound
      simp only [limbs]
      cases result : (limb tape 8 s).1 with
      | none => exact limb_remaining_le tape 8 s bound
      | some value => exact ih _ (limb_remaining_le tape 8 s bound)

theorem limbs_remaining_lt (tape : Tape) : ∀ n s,
    s.current.remaining.length < 8 →
      (limbs tape n s).2.current.remaining.length < 8 := by
  intro n
  induction n with
  | zero => intro s bound; exact bound
  | succ n ih =>
      intro s bound
      simp only [limbs]
      cases result : (limb tape 8 s).1 with
      | none => exact limb_remaining_lt tape 8 s bound
      | some value => exact ih _ (limb_remaining_lt tape 8 s bound)

theorem limbs_succ_remaining_lt (tape : Tape) (n : Nat) (s : TraceStream)
    (bound : s.current.remaining.length ≤ 8) :
    (limbs tape (n+1) s).2.current.remaining.length < 8 := by
  simp only [limbs]
  have first := limb_succ_remaining_lt tape 7 s bound
  cases result : (limb tape 8 s).1 with
  | none => exact first
  | some value => exact limbs_remaining_lt tape n _ first

theorem limbs_draws_le (tape : Tape) : ∀ n s,
    (limbs tape n s).2.draws ≤ s.draws + 8 * n := by
  intro n
  induction n with
  | zero => intro s; simp [limbs]
  | succ n ih =>
      intro s
      simp only [limbs]
      cases result : (limb tape 8 s).1 with
      | none =>
          simp only [result]
          have first := limb_draws_le tape 8 s
          omega
      | some value =>
          simp only [result]
          have first := limb_draws_le tape 8 s
          have rest := ih (limb tape 8 s).2
          omega

theorem limbs_draws_mono (tape : Tape) : ∀ n s,
    s.draws ≤ (limbs tape n s).2.draws := by
  intro n
  induction n with
  | zero => intro s; exact Nat.le_refl _
  | succ n ih =>
      intro s
      simp only [limbs]
      cases result : (limb tape 8 s).1 with
      | none => simpa [result] using limb_draws_mono tape 8 s
      | some value =>
          simp only [result]
          exact Nat.le_trans (limb_draws_mono tape 8 s) (ih _)

theorem limbs_succ_draws_lt (tape : Tape) (n : Nat) (s : TraceStream) :
    s.draws < (limbs tape (n+1) s).2.draws := by
  simp only [limbs]
  have first := limb_succ_draws_lt tape 7 s
  cases result : (limb tape 8 s).1 with
  | none => exact first
  | some value =>
      have mono := limbs_draws_mono tape n (limb tape 8 s).2
      have first' : s.draws < (limb tape 8 s).2.draws := by simpa using first
      have combined :
          s.draws < (limbs tape n (limb tape 8 s).2).2.draws := by omega
      simpa [result] using combined

structure ChallengeTrace where
  result : Option (List Nat)
  final : Transcript
  blocks : List Block
  draws : Nat
  drawn : List Nat
  remaining : List Nat

def challenge (tape : Tape) (s : Transcript) : ChallengeTrace :=
  let first := squeeze tape s
  let run := limbs tape 4 ⟨⟨first.2, words first.1⟩, [first.1], 0, []⟩
  ⟨run.1, run.2.current.transcript, run.2.blocks, run.2.draws,
    run.2.drawn, run.2.current.remaining⟩

/-- The trace is instrumentation of the existing challenge, not a replacement
sampler.  Both the returned value and exact final transcript are unchanged. -/
theorem challenge_erase (tape : Tape) (s : Transcript) :
    (challenge tape s).result =
        (FSBoundedTranscript.challenge tape s).1 ∧
      (challenge tape s).final =
        (FSBoundedTranscript.challenge tape s).2 := by
  simp only [challenge, FSBoundedTranscript.challenge]
  have exactRun := limbs_erase tape 4
    ⟨⟨(squeeze tape s).2, words (squeeze tape s).1⟩,
      [(squeeze tape s).1], 0, []⟩
  exact ⟨exactRun.1, congrArg Stream.transcript exactRun.2⟩

/-- The recorded blocks are content-exact: their flattened current words are
the words actually read followed by the still-unused words in the final
block.  The draw counter is the length of that actual read prefix. -/
theorem challenge_content (tape : Tape) (s : Transcript) :
    (challenge tape s).blocks.flatMap words =
        (challenge tape s).drawn ++ (challenge tape s).remaining ∧
      (challenge tape s).drawn.length = (challenge tape s).draws := by
  let first := squeeze tape s
  let initial : TraceStream :=
    ⟨⟨first.2, words first.1⟩, [first.1], 0, []⟩
  have initialContent : Content initial := by
    simp [initial, Content]
  have initialCount : DrawCount initial := by
    simp [initial, DrawCount]
  change Content (limbs tape 4 initial).2 ∧
    DrawCount (limbs tape 4 initial).2
  exact ⟨limbs_content tape 4 initial initialContent,
    limbs_drawCount tape 4 initial initialCount⟩

theorem challenge_balance (tape : Tape) (s : Transcript) :
    8 * (challenge tape s).blocks.length =
        (challenge tape s).draws + (challenge tape s).remaining.length ∧
      (challenge tape s).remaining.length < 8 := by
  let initial : TraceStream :=
    ⟨⟨(squeeze tape s).2, words (squeeze tape s).1⟩,
      [(squeeze tape s).1], 0, []⟩
  have initialBalanced : Balanced initial := by
    simp [initial, Balanced, words_length]
  have balanced := limbs_balanced tape 4 initial initialBalanced
  have remaining := limbs_succ_remaining_lt tape 3 initial (by
    simp [initial, words_length])
  change Balanced (limbs tape 4 initial).2 ∧
    (limbs tape 4 initial).2.current.remaining.length < 8
  exact ⟨balanced, remaining⟩

/-- The instrumented execution contains precisely one to four real squeeze
blocks.  The upper bound follows from the four eight-try limbs and the exact
eight-word block invariant; no ghost padding is counted. -/
theorem challenge_blocks_bounds (tape : Tape) (s : Transcript) :
    0 < (challenge tape s).blocks.length ∧
      (challenge tape s).blocks.length ≤ 4 := by
  let initial : TraceStream :=
    ⟨⟨(squeeze tape s).2, words (squeeze tape s).1⟩,
      [(squeeze tape s).1], 0, []⟩
  let run := limbs tape 4 initial
  have initialBalanced : Balanced initial := by
    simp [initial, Balanced, words_length]
  have balanced : Balanced run.2 := limbs_balanced tape 4 initial initialBalanced
  have draws : run.2.draws ≤ initial.draws + 8 * 4 := limbs_draws_le tape 4 initial
  have positiveDraw : initial.draws < run.2.draws := by
    simpa [run] using limbs_succ_draws_lt tape 3 initial
  have remaining : run.2.current.remaining.length < 8 := by
    simpa [run] using limbs_succ_remaining_lt tape 3 initial (by
      simp [initial, words_length])
  change 0 < run.2.blocks.length ∧ run.2.blocks.length ≤ 4
  constructor
  · have equation := balanced
    simp only [Balanced] at equation
    simp [initial] at positiveDraw
    omega
  · have equation := balanced
    simp only [Balanced] at equation
    simp [initial] at draws
    omega

/-- The final transcript is reached by exactly the recorded one-to-four
source squeezes, in order.  This is the causal state counterpart of
`challenge_erase`; no future or padded block occurs in the path. -/
theorem challenge_squeezePath (tape : Tape) (s : Transcript) :
    SqueezePath tape s (challenge tape s).blocks (challenge tape s).final := by
  let first := squeeze tape s
  let initial : TraceStream :=
    ⟨⟨first.2, words first.1⟩, [first.1], 0, []⟩
  have initialPath : SqueezePath tape s initial.blocks
      initial.current.transcript := by
    simpa [initial, first] using
      SqueezePath.snoc (SqueezePath.nil s : SqueezePath tape s [] s)
  change SqueezePath tape s (limbs tape 4 initial).2.blocks
    (limbs tape 4 initial).2.current.transcript
  exact limbs_path tape s 4 initial initialPath

#print axioms nextWord_erase
#print axioms limb_erase
#print axioms limbs_erase
#print axioms challenge_erase
#print axioms challenge_blocks_bounds
#print axioms challenge_squeezePath

end AspisV8Completion.FSLiveChallengeTrace
