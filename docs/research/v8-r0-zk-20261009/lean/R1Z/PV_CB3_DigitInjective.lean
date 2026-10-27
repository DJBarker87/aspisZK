import R1Z.PV_CB3_SamplerCarry
namespace R1Z.PV_CB3_DigitInjective
open PV_CB3_SamplerCarry
set_option autoImplicit false

/-- Canonical equal-length digit vectors are determined by their value.
This is the bridge from rank arithmetic to exact array equality. -/
theorem value_injective (base : Nat) (positive : 0 < base)
    (xs ys : List Nat) (same_length : xs.length = ys.length)
    (xc : ∀ d, d ∈ xs → d < base) (yc : ∀ d, d ∈ ys → d < base)
    (same_value : value base xs = value base ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp only [List.length_nil, List.length_cons] at same_length; omega
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_nil, List.length_cons] at same_length; omega
    | cons y ys =>
      have hx := xc x (List.mem_cons_self ..)
      have hy := yc y (List.mem_cons_self ..)
      have heads := congrArg (fun n => n % base) same_value
      simp only [value, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
        Nat.mod_eq_of_lt hy] at heads
      subst y
      have tails : value base xs = value base ys := by
        have hv : base * value base xs = base * value base ys := by
          simp only [value] at same_value
          omega
        exact Nat.eq_of_mul_eq_mul_left positive hv
      have heq := ih ys (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using same_length)
        (fun d h => xc d (List.mem_cons_of_mem x h))
        (fun d h => yc d (List.mem_cons_of_mem x h)) tails
      rw [heq]

#print axioms value_injective
end R1Z.PV_CB3_DigitInjective
