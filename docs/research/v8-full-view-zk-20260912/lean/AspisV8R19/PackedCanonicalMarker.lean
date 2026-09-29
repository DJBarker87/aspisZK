import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-! Exact high-bit replacement for the decoder's OR of canonicality flags.
All values here have already been masked to 31 bits, including invalid P.
This proves the integer predicate, not universal compiler/Rust refinement. -/
set_option autoImplicit false
namespace AspisV8R19.PackedCanonicalMarker

def p : Nat := 2147483647
def marks (xs : List Nat) := xs.foldr (fun v acc => (v+1) ||| acc) 0
def flags (xs : List Nat) := xs.foldr (fun v acc => (if v=p then 1 else 0) ||| acc) 0

theorem add_one_fits (v : Nat) (hv : v ≤ p) : v+1 < 2^32 := by
  simp only [p] at hv
  omega

theorem word_marker (v : Nat) (hv : v ≤ p) :
    (v+1) >>> 31 = if v=p then 1 else 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  simp only [p] at *
  split_ifs <;> omega

theorem shifted_marks (xs : List Nat) (hv : ∀ v ∈ xs, v ≤ p) :
    marks xs >>> 31 = flags xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [marks,flags,List.foldr_cons,Nat.shiftRight_or_distrib]
      rw [word_marker x (hv x (by simp))]
      exact congrArg (fun z => (if x=p then 1 else 0) ||| z)
        (ih (fun v h => hv v (List.mem_cons_of_mem x h)))

theorem flags_zero_iff (xs : List Nat) : flags xs = 0 ↔ ∀ v ∈ xs, v ≠ p := by
  induction xs with
  | nil => simp [flags]
  | cons x xs ih =>
      by_cases hx : x=p
      · constructor
        · intro h
          have hb := congrArg (fun n : Nat => n.testBit 0) h
          simp [flags,hx] at hb
        · intro h
          exact False.elim ((h x (by simp)) hx)
      · simpa [flags,hx] using ih

theorem source_check_equivalent (xs : List Nat) (hv : ∀ v ∈ xs, v ≤ p) :
    marks xs >>> 31 = 0 ↔ ∀ v ∈ xs, v < p := by
  rw [shifted_marks xs hv,flags_zero_iff]
  constructor
  · intro h v hvx; have := hv v hvx; have := h v hvx; omega
  · intro h v hvx; have := h v hvx; omega

#print axioms add_one_fits
#print axioms word_marker
#print axioms shifted_marks
#print axioms flags_zero_iff
#print axioms source_check_equivalent
end AspisV8R19.PackedCanonicalMarker
