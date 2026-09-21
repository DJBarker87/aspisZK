import Mathlib.Logic.Function.Basic
import Lean.Elab.Tactic.Omega

/-! Universal storage model for ascending in-place arity-four folding.
`combine` is arbitrary, so the proof changes no arithmetic formula. This
is not extracted Rust semantics or a proof of the entire verifier. -/
set_option autoImplicit false
namespace AspisV8R17.InPlaceDenseFold
variable {K : Type*}

def run (combine : K → K → K → K → K) (initial : Nat → K) : Nat → Nat → K
  | 0 => initial
  | n+1 =>
    let old := run combine initial n
    Function.update old n
      (combine (old (4*n)) (old (4*n+1)) (old (4*n+2)) (old (4*n+3)))

/-- A future input block has not been overwritten by any completed output. -/
theorem unread (combine : K → K → K → K → K) (initial : Nat → K)
    (n j k : Nat) (h : n ≤ j) :
    run combine initial n (4*j+k) = initial (4*j+k) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [run, Function.update_of_ne (by omega : 4*j+k ≠ n)]
    exact ih j (by omega)

/-- Every completed output equals the allocating reference's original block. -/
theorem written (combine : K → K → K → K → K) (initial : Nat → K)
    (n i : Nat) (h : i < n) :
    run combine initial n i =
      combine (initial (4*i)) (initial (4*i+1))
        (initial (4*i+2)) (initial (4*i+3)) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      rw [run, Function.update_self]
      have h0 := unread combine initial n n 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [h0, unread combine initial n n 1 (by omega),
        unread combine initial n n 2 (by omega), unread combine initial n n 3 (by omega)]
    · rw [run, Function.update_of_ne he]
      exact ih i (by omega)

/-- The source's integer-division loop bound makes all four reads valid. -/
theorem read_in_bounds (len i : Nat) (h : i < len / 4) :
    4*i+3 < len ∧ i < len := by
  omega

#print axioms unread
#print axioms written
#print axioms read_in_bounds
end AspisV8R17.InPlaceDenseFold
