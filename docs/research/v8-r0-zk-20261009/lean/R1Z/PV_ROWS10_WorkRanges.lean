import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace R1Z.PV_ROWS10_WorkRanges
/-- Natural-number interpretation of the frozen native_workers::range body.
This is a source arithmetic helper; no thread execution is asserted. -/
def start (n k : Nat) : Nat := n / 16 * k + min k (n % 16)
def stop (n k : Nat) : Nat := start n k + n / 16 + if k < n % 16 then 1 else 0
 theorem zero_start (n : Nat) : start n 0 = 0 := by simp [start]
 theorem adjacent (n k : Nat) : stop n k = start n (k+1) := by
  unfold stop start
  rw [Nat.mul_succ]
  by_cases h : k < n % 16
  · have h1 : k ≤ n % 16 := by omega
    have h2 : k+1 ≤ n % 16 := by omega
    simp only [if_pos h, Nat.min_eq_left h1, Nat.min_eq_left h2]
    omega
  · have h1 : n % 16 ≤ k := by omega
    have h2 : n % 16 ≤ k+1 := by omega
    simp only [if_neg h, Nat.min_eq_right h1, Nat.min_eq_right h2]
    omega
 theorem end_last (n : Nat) : stop n 15 = n := by
  rw [adjacent]
  unfold start
  have h : n % 16 ≤ 16 := Nat.le_of_lt (Nat.mod_lt n (by decide))
  rw [Nat.min_eq_right h]
  have hd := Nat.mod_add_div n 16
  rw [Nat.mul_comm 16 (n/16)] at hd
  omega
 theorem ordered (n k : Nat) (hk : k ≤ 16) : start n k ≤ n := by
  have hm := Nat.min_le_right k (n%16)
  have hq := Nat.mul_le_mul_left (n/16) hk
  have hd := Nat.mod_add_div n 16
  rw [Nat.mul_comm 16 (n/16)] at hd
  unfold start
  omega
 theorem range_bounds (n k : Nat) (hk : k < 16) :
    start n k ≤ stop n k ∧ stop n k ≤ n := by
  constructor
  · unfold stop; omega
  · rw [adjacent]; apply ordered; omega
/-- Every machine arithmetic intermediate of the range body is bounded by n.
The separate structural binding must still supply usize's width and the
admitted k guard; this theorem does not model spawn, join or panic. -/
 theorem intermediate_bounds (n k limit : Nat) (hn : n ≤ limit) (hk : k < 16) :
    n/16*k ≤ limit ∧ start n k ≤ limit ∧ start n k+n/16 ≤ limit ∧ stop n k ≤ limit := by
  have hs := range_bounds n k hk
  have hq : n/16*k ≤ start n k := by unfold start; omega
  have hi : start n k+n/16 ≤ stop n k := by unfold stop; omega
  omega
#print axioms zero_start
#print axioms adjacent
#print axioms end_last
#print axioms ordered
#print axioms range_bounds
#print axioms intermediate_bounds
end R1Z.PV_ROWS10_WorkRanges
