import AspisV8R19.SamplerWords

/-! Reuses the retained V5QuerySamplerControl scan order/argument, with the
actual V8 q22 constants. No V5 18-query theorem is treated as a V8 theorem. -/
set_option autoImplicit false
namespace AspisV8R19.Q22WordScan

structure ScanState where
  accepted : List Nat
  draws : Nat
  deriving Repr, DecidableEq

def keep (xs : List Nat) (x : Nat) : List Nat := if x ∈ xs then xs else xs ++ [x]
def scan : ScanState → List Nat → ScanState × Bool
  | s,[] => (s,false)
  | s,x::xs =>
      if s.accepted.length = 22 ∨ s.draws = 64 then (s,true)
      else scan ⟨keep s.accepted x,s.draws+1⟩ xs

def finish (s : ScanState) : Except Nat (List Nat) :=
  if s.accepted.length = 22 then .ok s.accepted else .error s.accepted.length

theorem scan_progress (s : ScanState) (xs : List Nat) (h : (scan s xs).2 = false) :
    (scan s xs).1.draws = s.draws + xs.length := by
  induction xs generalizing s with
  | nil => simp [scan]
  | cons x xs ih =>
      by_cases stop : s.accepted.length = 22 ∨ s.draws = 64
      · simp [scan,stop] at h
      · simp only [scan,if_neg stop] at h ⊢
        have hi := ih ⟨keep s.accepted x,s.draws+1⟩ h
        simp only [List.length_cons] at *
        omega

theorem scan_draw_cap (s : ScanState) (xs : List Nat) (h : s.draws ≤ 64) :
    (scan s xs).1.draws ≤ 64 := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih =>
      simp only [scan]
      split_ifs with stop
      · exact h
      · apply ih
        dsimp only
        have hn : s.draws ≠ 64 := fun he => stop (Or.inr he)
        omega

theorem keep_length (xs : List Nat) (x : Nat) : (keep xs x).length ≤ xs.length+1 := by
  by_cases h : x ∈ xs <;> simp [keep,h]

theorem scan_count_cap (s : ScanState) (xs : List Nat) (h : s.accepted.length ≤ 22) :
    (scan s xs).1.accepted.length ≤ 22 := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih =>
      simp only [scan]
      split_ifs with stop
      · exact h
      · apply ih
        have hn : s.accepted.length ≠ 22 := fun he => stop (Or.inl he)
        have hk := keep_length s.accepted x
        dsimp only
        omega

theorem scan_complete (s : ScanState) (x : Nat) (xs : List Nat)
    (h : s.accepted.length = 22) : scan s (x::xs) = (s,true) := by simp [scan,h]

theorem scan_empty_does_not_detect (s : ScanState) : scan s [] = (s,false) := rfl

theorem finish_error_count (s : ScanState) (h : s.accepted.length ≠ 22) :
    finish s = .error s.accepted.length := by simp [finish,h]

#print axioms scan_progress
#print axioms scan_draw_cap
#print axioms keep_length
#print axioms scan_count_cap
#print axioms scan_complete
#print axioms scan_empty_does_not_detect
#print axioms finish_error_count
end AspisV8R19.Q22WordScan
