import FSBoundedTranscript
set_option autoImplicit false
namespace AspisV8Completion.FSChallengeCanonical
open FSBoundedTranscript
def WordsValid (xs : List Nat) : Prop := ∀ x ∈ xs, x < 2147483648

theorem words_valid (b : Block) : WordsValid (words b) := by
  intro x mem
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
  exact Nat.mod_lt _ (by decide)

theorem words_length (b : Block) : (words b).length = 8 := by
  simp only [words, List.length_map, List.length_range]

theorem next_valid (tape : Tape) (s : Stream) (valid : WordsValid s.remaining) :
    (nextWord tape s).1 < 2147483648 ∧ WordsValid (nextWord tape s).2.remaining := by
  cases hs : s.remaining with
  | cons x xs =>
      simp only [nextWord, hs]
      constructor
      · exact valid x (by simp [hs])
      · intro y hy; exact valid y (by simp [hs, hy])
  | nil =>
      have all := words_valid (squeeze tape s.transcript).1
      have len := words_length (squeeze tape s.transcript).1
      cases hw : words (squeeze tape s.transcript).1 with
      | nil => simp only [hw, List.length_nil] at len; contradiction
      | cons x xs =>
          simp only [nextWord, hs, hw]
          change x < 2147483648 ∧ WordsValid xs
          constructor
          · exact all x (by simp [hw])
          · intro y hy; exact all y (by simp [hw, hy])

theorem limb_canonical (tape : Tape) : ∀ n (s : Stream), WordsValid s.remaining →
    WordsValid (limb tape n s).2.remaining ∧
      ∀ x, (limb tape n s).1 = some x → x < 2147483647 := by
  intro n
  induction n with
  | zero => intro s valid; exact ⟨valid, by intro x hx; cases hx⟩
  | succ n ih =>
      intro s valid
      have step := next_valid tape s valid
      simp only [limb]
      split
      · exact ih _ step.2
      · refine ⟨step.2, ?_⟩
        intro x hx
        cases hx
        omega

theorem limbs_canonical (tape : Tape) : ∀ n (s : Stream), WordsValid s.remaining →
    WordsValid (limbs tape n s).2.remaining ∧
      ∀ xs, (limbs tape n s).1 = some xs →
        xs.length = n ∧ ∀ x ∈ xs, x < 2147483647 := by
  intro n
  induction n with
  | zero =>
      intro s valid
      refine ⟨valid, ?_⟩
      intro xs h; cases h
      exact ⟨rfl, by intro x hx; cases hx⟩
  | succ n ih =>
      intro s valid
      have first := limb_canonical tape 8 s valid
      have rest := ih (limb tape 8 s).2 first.1
      simp only [limbs]
      split
      · exact ⟨first.1, by intro xs hx; cases hx⟩
      · refine ⟨rest.1, ?_⟩
        intro xs h
        cases hr : (limbs tape n (limb tape 8 s).2).1 with
        | none => simp only [hr, Option.map_none] at h; cases h
        | some tail =>
            simp only [hr, Option.map_some, Option.some.injEq] at h
            subst xs
            obtain ⟨hlen, hall⟩ := rest.2 tail hr
            constructor
            · simp only [List.length_cons, hlen]
            · intro y hy
              simp only [List.mem_cons] at hy
              rcases hy with rfl | hy
              · exact first.2 _ (by assumption)
              · exact hall y hy

theorem challenge_canonical (tape : Tape) (s : Transcript) (xs : List Nat)
    (success : (challenge tape s).1 = some xs) :
    xs.length = 4 ∧ ∀ x ∈ xs, x < 2147483647 :=
  (limbs_canonical tape 4 ⟨(squeeze tape s).2, words (squeeze tape s).1⟩
    (words_valid _)).2 xs success

#print axioms challenge_canonical
end AspisV8Completion.FSChallengeCanonical
