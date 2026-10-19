import AspisV8R19.Q22SamplerProgram

set_option autoImplicit false
namespace AspisV8R19.Q22SamplerInvariants
open DuplexFrames SourceDuplexStep SamplerWords Q22WordScan Q22SamplerProgram

def Valid (s : ScanState) : Prop := s.accepted.Nodup ∧ s.accepted.length ≤ 22 ∧
  ∀ x ∈ s.accepted, x < 262144

def ResultValid : Except Nat (List Nat) → Prop
  | .error n => n ≤ 21
  | .ok xs => xs.Nodup ∧ xs.length = 22 ∧ ∀ x ∈ xs, x < 262144

theorem keep_nodup (xs : List Nat) (x : Nat) (h : xs.Nodup) : (keep xs x).Nodup := by
  by_cases hx : x ∈ xs <;> simp [keep,hx,List.nodup_append,h]
  intro a ha he
  exact hx (he ▸ ha)

theorem keep_bounded (xs : List Nat) (x : Nat) (h : ∀ y ∈ xs, y < 262144)
    (hx : x < 262144) : ∀ y ∈ keep xs x, y < 262144 := by
  intro y hy
  by_cases hmem : x ∈ xs
  · exact h y (by simpa [keep,hmem] using hy)
  · have hy' : y ∈ xs ∨ y = x := by simpa [keep,hmem] using hy
    rcases hy' with old | rfl
    · exact h y old
    · exact hx

theorem scan_valid (s : ScanState) (xs : List Nat) (h : Valid s)
    (hx : ∀ x ∈ xs, x < 262144) : Valid (scan s xs).1 := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih =>
      by_cases stop : s.accepted.length = 22 ∨ s.draws = 64
      · simpa [scan,stop] using h
      · simp only [scan,if_neg stop]
        apply ih
        · refine ⟨keep_nodup _ _ h.1,?_,keep_bounded _ _ h.2.2 (hx x (by simp))⟩
          have hl := keep_length s.accepted x
          have hn : s.accepted.length ≠ 22 := fun he => stop (Or.inl he)
          have bound := h.2.1
          change (keep s.accepted x).length ≤ 22
          omega
        · intro y hy; exact hx y (by simp [hy])

theorem finish_valid (s : ScanState) (h : Valid s) : ResultValid (finish s) := by
  unfold finish
  split_ifs with complete
  · exact ⟨h.1,complete,h.2.2⟩
  · change s.accepted.length ≤ 21
    have bound := h.2.1
    omega

theorem source_exec_valid (H : Bytes → State) (s : State) (q : ScanState)
    (r : MemoizedProgramLaw.View Bytes State Result) (exec : SourceExec H s q r)
    (h : Valid q) : ResultValid r.2.1 := by
  induction exec with
  | done s q cap => exact finish_valid q h
  | stop s q draw stopped =>
      apply finish_valid
      apply scan_valid q _ h
      intro x hx
      exact words_bounded 18 (step H s).1 x hx
  | more s q draw going tail rest ih =>
      apply ih
      apply scan_valid q _ h
      intro x hx
      exact words_bounded 18 (step H s).1 x hx

theorem challenge_result_valid (H : Bytes → State) (s : State) :
    ResultValid (challengeRun H s).2.1 :=
  source_exec_valid H s ⟨[],0⟩ _ (no_artificial_cutoff H s) (by simp [Valid])

#print axioms keep_nodup
#print axioms keep_bounded
#print axioms scan_valid
#print axioms finish_valid
#print axioms source_exec_valid
#print axioms challenge_result_valid
end AspisV8R19.Q22SamplerInvariants
