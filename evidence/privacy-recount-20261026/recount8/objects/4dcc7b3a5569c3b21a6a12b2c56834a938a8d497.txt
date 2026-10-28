import R1Z.PV_RunJoin_SampleDomain34
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WorkRange35

/-- Integer formulas of native_workers::range; this is the arithmetic
model. Native overflow, scheduling, panic, TLS and allocation links remain P. -/
def start (n k : Nat) : Nat := (n/16)*k+min k (n%16)
def width (n k : Nat) : Nat := n/16 + if k<n%16 then 1 else 0

theorem zero (n : Nat) : start n 0=0 := by simp only [start,Nat.mul_zero,Nat.zero_min,Nat.add_zero]

theorem next (n k : Nat) : start n (k+1)=start n k+width n k := by
  unfold start width
  simp only [Nat.mul_add,Nat.mul_one]
  by_cases h : k<n%16
  · rw [if_pos h,Nat.min_eq_left (by omega),Nat.min_eq_left (by omega)];omega
  · rw [if_neg h,Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)];omega

theorem end_all (n : Nat) : start n 16=n := by
  have h := Nat.mod_lt n (by decide : 0<16)
  have d := Nat.mod_add_div n 16
  unfold start
  rw [Nat.min_eq_right (by omega)]
  omega

theorem monotone (n : Nat) {a b : Nat} (h : a≤b) : start n a≤start n b := by
  unfold start
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h) (by omega)

theorem bounded (n k : Nat) (hk : k<16) :
    start n k≤start n k+width n k ∧ start n k+width n k≤n := by
  constructor
  · omega
  · rw [← next]
    exact (monotone n (by omega : k+1≤16)).trans_eq (end_all n)

#print axioms zero
#print axioms next
#print axioms end_all
#print axioms monotone
#print axioms bounded
end R1Z.PV_RunJoin_WorkRange35
