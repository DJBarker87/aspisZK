import QueryScanOrderedModel

/-! Deterministic row-31 invariants. No transcript is evaluated: induction
follows the scan's stop/duplicate/fresh branches, for arbitrary input blocks. -/
set_option autoImplicit false
namespace AspisR1.QueryScanRow31Invariant
open AspisV8R19.Q22WordScan AspisV8R19.SamplerWords
open AspisV8R19.SourceDuplexStep

/-- Fresh appends preserve a predicate; duplicates preserve the existing list. -/
theorem keep_all (p : Nat → Prop) (xs : List Nat) (x : Nat)
    (hs : ∀ y ∈ xs, p y) (hx : p x) : ∀ y ∈ keep xs x, p y := by
  intro y hy
  rcases (QueryScanModelFailure.keep_mem xs x y).mp hy with hy | rfl
  · exact hs y hy
  · exact hx

/-- Loop invariant for any per-index predicate, including the 18-bit bound. -/
theorem scan_all (p : Nat → Prop) (s : ScanState) (xs : List Nat)
    (hs : ∀ y ∈ s.accepted, p y) (hx : ∀ y ∈ xs, p y) :
    ∀ y ∈ (scan s xs).1.accepted, p y := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih =>
    by_cases stop : s.accepted.length = 22 ∨ s.draws = 64
    · simpa only [scan, if_pos stop] using hs
    · simp only [scan, if_neg stop]
      exact ih ⟨keep s.accepted x, s.draws + 1⟩
        (keep_all p _ x hs (hx x (by simp)))
        (fun y hy => hx y (List.mem_cons_of_mem x hy))

/-- The finish guard rejects every state with fewer than 22 collected values. -/
theorem finish_rejects_short (s : ScanState) (h : s.accepted.length < 22) :
    finish s = .error s.accepted.length :=
  finish_error_count s (by omega)

/-- Success packages all three invariants. This applies to any candidate stream. -/
theorem successful_scan (xs out : List Nat)
    (hb : ∀ x ∈ xs, x < 262144)
    (h : finish (scan QueryScanModelFailure.initial xs).1 = .ok out) :
    out.Nodup ∧ out.length = 22 ∧ ∀ x ∈ out, x < 262144 := by
  have hn : QueryScanModelFailure.initial.accepted.Nodup := List.nodup_nil
  obtain ⟨hlen, hnodup, _⟩ := QueryScanOrderedModel.successful_output _ xs out hn h
  have hall := scan_all (fun x => x < 262144) QueryScanModelFailure.initial xs
    (by simp [QueryScanModelFailure.initial]) hb
  have he : (scan QueryScanModelFailure.initial xs).1.accepted = out := by
    unfold finish at h
    split at h
    · exact Except.ok.inj h
    · cases h
  exact ⟨hnodup, hlen, he ▸ hall⟩

/-- Same stop-before-word block driver as the retained source recurrence. -/
def scanBlocks (blocks : List State) : Except Nat (List Nat) :=
  finish (QueryScanOrderedModel.blockRun QueryScanModelFailure.initial
    (blocks.map (words 18))).1

theorem block_words_bounded (blocks : List State) :
    ∀ x ∈ (blocks.map (words 18)).flatten, x < 262144 := by
  intro x hx
  obtain ⟨ws, hws, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨block, _, rfl⟩ := List.mem_map.mp hws
  exact words_bounded 18 block x hx

/-- Successful row-31 scanning of arbitrary blocks yields 22 distinct 18-bit indices. -/
theorem successful_blocks (blocks : List State) (out : List Nat)
    (h : scanBlocks blocks = .ok out) :
    out.Nodup ∧ out.length = 22 ∧ ∀ x ∈ out, x < 262144 := by
  unfold scanBlocks at h
  rw [QueryScanOrderedModel.blocks_flatten] at h
  exact successful_scan _ out (block_words_bounded blocks) h

/-- Also expose the stable first-22 order, rather than just set cardinality. -/
theorem successful_blocks_order (blocks : List State) (out : List Nat)
    (h : scanBlocks blocks = .ok out) :
    out = ((blocks.map (words 18)).flatten.foldl keep []).take 22 := by
  unfold scanBlocks at h
  rw [QueryScanOrderedModel.blocks_flatten] at h
  exact QueryScanOrderedModel.successful_first22 _ _ out List.nodup_nil h

#print axioms keep_all
#print axioms scan_all
#print axioms finish_rejects_short
#print axioms successful_scan
#print axioms block_words_bounded
#print axioms successful_blocks
#print axioms successful_blocks_order
end AspisR1.QueryScanRow31Invariant
