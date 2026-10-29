import QueryScanModelFailure

/-! Ordered, stable dedup and block/word recurrence correspondence for the
retained Q22 model. Source-library and extraction correspondence are separate. -/
set_option autoImplicit false
namespace AspisR1.QueryScanOrderedModel
open AspisV8R19.Q22WordScan

 theorem keep_prefix (xs : List Nat) (x : Nat) : xs <+: keep xs x := by
  by_cases h : x ∈ xs
  · simp [keep, h]
  · exact ⟨[x], by simp [keep, h]⟩

 theorem fold_keep_prefix (xs ys : List Nat) : xs <+: ys.foldl keep xs := by
  induction ys generalizing xs with
  | nil => exact ⟨[], by simp [scan]⟩
  | cons y ys ih => exact (keep_prefix xs y).trans (ih (keep xs y))

 /-- The accepted output is a prefix of stable first-occurrence deduplication.
 It is never sorted or reordered by the Q22 recurrence. -/
 theorem scan_order_prefix (s : ScanState) (xs : List Nat) :
    (scan s xs).1.accepted <+: xs.foldl keep s.accepted := by
  induction xs generalizing s with
  | nil => exact ⟨[], by simp [scan]⟩
  | cons x xs ih =>
    by_cases hs : s.accepted.length = 22 ∨ s.draws = 64
    · simp only [scan, if_pos hs, List.foldl_cons]
      exact (keep_prefix _ _).trans (fold_keep_prefix _ _)
    · simpa only [scan, if_neg hs, List.foldl_cons] using
        ih ⟨keep s.accepted x, s.draws+1⟩

 theorem keep_nodup (xs : List Nat) (x : Nat) (h : xs.Nodup) :
    (keep xs x).Nodup := by
  by_cases hx : x ∈ xs
  · simpa [keep, hx] using h
  · simpa [keep, hx] using h.concat hx

 theorem scan_nodup (s : ScanState) (xs : List Nat) (h : s.accepted.Nodup) :
    (scan s xs).1.accepted.Nodup := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih =>
    by_cases hs : s.accepted.length = 22 ∨ s.draws = 64
    · simpa only [scan, if_pos hs] using h
    · simpa only [scan, if_neg hs] using
        ih ⟨keep s.accepted x, s.draws+1⟩ (keep_nodup _ _ h)

 theorem scan_stop_state (s : ScanState) (xs : List Nat)
    (hs : s.accepted.length = 22 ∨ s.draws = 64) : (scan s xs).1 = s := by
  cases xs <;> simp [scan, hs]

 theorem scan_append_state (s : ScanState) (xs ys : List Nat) :
    (scan s (xs ++ ys)).1 = (scan (scan s xs).1 ys).1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    by_cases hs : s.accepted.length = 22 ∨ s.draws = 64
    · simp only [List.cons_append, scan, if_pos hs]
      exact (scan_stop_state s ys hs).symm
    · simpa only [List.cons_append, scan, if_neg hs] using
        ih ⟨keep s.accepted x, s.draws+1⟩

 theorem scan_true_stopped (s : ScanState) (xs : List Nat)
    (h : (scan s xs).2 = true) :
    (scan s xs).1.accepted.length = 22 ∨ (scan s xs).1.draws = 64 := by
  induction xs generalizing s with
  | nil => simp [scan] at h
  | cons x xs ih =>
    by_cases hs : s.accepted.length = 22 ∨ s.draws = 64
    · simpa only [scan, if_pos hs] using hs
    · simp only [scan, if_neg hs] at h ⊢
      exact ih _ h

 /-- Number of consumed blocks. The stop test is inside scan, before a word,
 so a completed eighth word is detected in the following nonempty block. -/
 def blockRun (s : ScanState) : List (List Nat) → ScanState × Nat
  | [] => (s, 0)
  | b :: bs =>
    let r := scan s b
    if r.2 then (r.1, 1)
    else let tail := blockRun r.1 bs; (tail.1, tail.2+1)

 theorem blocks_flatten (s : ScanState) (bs : List (List Nat)) :
    (blockRun s bs).1 = (scan s bs.flatten).1 := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [blockRun, List.flatten_cons]
    by_cases hs : (scan s b).2 = true
    · simp only [hs, if_true]
      rw [scan_append_state]
      exact (scan_stop_state _ _ (scan_true_stopped s b hs)).symm
    · simp only [hs, Bool.false_eq_true, if_false]
      rw [ih, scan_append_state]

 theorem block_count_le (s : ScanState) (bs : List (List Nat)) :
    (blockRun s bs).2 ≤ bs.length := by
  induction bs generalizing s with
  | nil => simp [blockRun]
  | cons b bs ih =>
    simp only [blockRun]
    split
    · simp
    · have h := ih (scan s b).1
      simp only [List.length_cons]
      omega

 /-- Successful finish exposes exactly 22 distinct indices in stable scan order. -/
 theorem successful_output (s : ScanState) (xs out : List Nat)
    (hn : s.accepted.Nodup) (h : finish (scan s xs).1 = .ok out) :
    out.length = 22 ∧ out.Nodup ∧ out <+: xs.foldl keep s.accepted := by
  unfold finish at h
  split at h
  · have he : (scan s xs).1.accepted = out := Except.ok.inj h
    exact ⟨he ▸ ‹_›, he ▸ scan_nodup s xs hn, he ▸ scan_order_prefix s xs⟩
  · cases h

/-- The successful array order corresponds to the first 22 stable distinct
values of the candidate-word stream, including partial final blocks. -/
 theorem successful_first22 (s : ScanState) (xs out : List Nat)
    (hn : s.accepted.Nodup) (h : finish (scan s xs).1 = .ok out) :
    out = (xs.foldl keep s.accepted).take 22 := by
  obtain ⟨hlen, _, tail, htail⟩ := successful_output s xs out hn h
  rw [← htail]
  exact (List.take_left' hlen).symm

 theorem block_failure_smallRange {N : Nat} (w : Fin 64 → Fin N)
    (bs : List (List Nat)) (hwords : bs.flatten = QueryScanModelFailure.words w)
    (count : Nat)
    (hfail : finish (blockRun QueryScanModelFailure.initial bs).1 = .error count) :
    QueryScanExhaustion.smallRange w 21 := by
  apply QueryScanModelFailure.failure_smallRange w
  unfold QueryScanModelFailure.fails
  rw [blocks_flatten, hwords] at hfail
  intro he
  simp only [finish, he, if_true] at hfail
  cases hfail

#print axioms keep_prefix
#print axioms fold_keep_prefix
#print axioms scan_order_prefix
#print axioms keep_nodup
#print axioms scan_nodup
#print axioms scan_stop_state
#print axioms scan_append_state
#print axioms scan_true_stopped
#print axioms blocks_flatten
#print axioms block_count_le
#print axioms successful_output
#print axioms successful_first22
#print axioms block_failure_smallRange
end AspisR1.QueryScanOrderedModel
