import PCD_Error
set_option autoImplicit false
namespace PCD_LaneLoop
open PCD
/-- Result of one source condition at each level, with exact first-error cut. -/
inductive Scan where
  | done (visited : Nat)
  | rejected (visited : Nat)
  deriving DecidableEq

def scan (test : Nat → Bool) (level remaining : Nat) : Scan :=
  match remaining with
  | 0 => .done level
  | n + 1 => if test level then scan test (level+1) n else .rejected level

def good (test : Nat → Bool) (level remaining : Nat) : Prop :=
  ∀ i, level ≤ i → i < level + remaining → test i = true

theorem scan_zero (test : Nat → Bool) (level : Nat) :
    scan test level 0 = .done level := rfl

theorem scan_reject (test : Nat → Bool) (level n : Nat)
    (h : test level = false) : scan test level (n+1) = .rejected level := by
  simp only [scan, h, Bool.false_eq_true, ↓reduceIte]

theorem scan_continue (test : Nat → Bool) (level n : Nat)
    (h : test level = true) : scan test level (n+1) = scan test (level+1) n := by
  simp only [scan, h, ↓reduceIte]

theorem scan_done_iff (test : Nat → Bool) (level n : Nat) :
    scan test level n = .done (level+n) ↔ good test level n := by
  induction n generalizing level with
  | zero => simp [scan, good]; omega
  | succ n ih =>
    by_cases h : test level = true
    · rw [scan_continue test level n h]
      have eq : level + (n+1) = (level+1)+n := by omega
      rw [eq, ih]
      constructor
      · intro g i lo hi
        by_cases e : i = level
        · simpa [e] using h
        · exact g i (by omega) (by omega)
      · intro g i lo hi
        exact g i (by omega) (by omega)
    · have hf : test level = false := by cases e : test level <;> simp_all
      rw [scan_reject test level n hf]
      constructor
      · intro impossible; cases impossible
      · intro g; exact False.elim (h (g level (by omega) (by omega)))

/-- A first failing level yields the exact abort-free comparison prefix.
This is a model law. Native loop association is NOT a hypothesis hidden here. -/
theorem first_failure (test : Nat → Bool) (level offset tail : Nat)
    (before : good test level offset) (bad : test (level+offset) = false) :
    scan test level (offset+tail+1) = .rejected (level+offset) := by
  induction offset generalizing level with
  | zero => simpa using scan_reject test level tail (by simpa using bad)
  | succ n ih =>
    have h : test level = true := before level (by omega) (by omega)
    rw [show n+1+tail+1 = (n+tail+1)+1 by omega, scan_continue test level _ h]
    have pref : good test (level+1) n := by
      intro i lo hi; exact before i (by omega) (by omega)
    have b : test ((level+1)+n) = false := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bad
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (level+1) pref b

#print axioms scan_zero
#print axioms scan_reject
#print axioms scan_continue
#print axioms scan_done_iff
#print axioms first_failure
end PCD_LaneLoop
