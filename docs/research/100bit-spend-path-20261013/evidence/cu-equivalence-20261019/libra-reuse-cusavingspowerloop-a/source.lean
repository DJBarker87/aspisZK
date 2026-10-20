import Mathlib.Algebra.BigOperators.Ring.List

/-! Semantic power-table loop: emit the current value before multiplying.
The theorem includes the final updated state, so it covers the unused final
update rather than silently deleting it. Extracted machine execution remains
a separate source binding. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsPowerLoop
variable {R : Type} [Monoid R]

def run (q p : R) : Nat → List R × R
  | 0 => ([],p)
  | n+1 => let tail := run q (p*q) n; (p::tail.1,tail.2)

theorem run_eq (q p : R) (n : Nat) :
    run q p n = ((List.range n).map (fun i => p*q^i),p*q^n) := by
  induction n generalizing p with
  | zero => simp [run]
  | succ n ih =>
    rw [run, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, pow_zero, mul_one]
    have hm (i : Nat) : p*q*q^i = p*q^(i+1) := by
      rw [pow_succ']
      exact mul_assoc p q (q^i)
    simp only [hm, Nat.succ_eq_add_one]

theorem initial_one (q : R) (n : Nat) :
    run q 1 n = ((List.range n).map (fun i => q^i),q^n) := by
  simp only [run_eq, one_mul]

theorem length (q p : R) (n : Nat) : (run q p n).1.length = n := by
  simp [run_eq]

theorem read (q : R) (n i : Nat) (hi : i < n) :
    (run q 1 n).1[i]? = some (q^i) := by
  simp only [initial_one, List.getElem?_map, List.getElem?_range hi, Option.map_some]

#print axioms run_eq
#print axioms initial_one
#print axioms length
#print axioms read
end AspisR1.CuSavingsPowerLoop
