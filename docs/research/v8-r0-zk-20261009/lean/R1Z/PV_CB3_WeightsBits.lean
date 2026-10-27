import R1Z.PV_CB3_WeightsDomain
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsBits

def digit (j d : Nat) : Nat := (j >>> (2*d)) &&& 3

theorem digit_bound (j d : Nat) : digit j d < 4 := by
  have h : (j >>> (2*d)) &&& 3 ≤ 3 := Nat.and_le_right
  unfold digit
  omega

theorem shifted_bound (x n : Nat) (hx : x < 4) (hn : n ≤ 8) : x <<< n < 2^10 := by
  rw [Nat.shiftLeft_eq]
  have hp : 2^n ≤ 2^8 := Nat.pow_le_pow_right (by decide) hn
  have hpos := Nat.two_pow_pos n
  have hmul := Nat.mul_lt_mul_of_pos_right hx hpos
  omega

def row (j : Nat) : Nat :=
  ((((digit j 0 <<< 6) ||| (digit j 1 <<< 8)) ||| (digit j 2 <<< 4)) ||| digit j 3) |||
    (digit j 4 <<< 2)

theorem row_bound (j : Nat) : row j < 1024 := by
  unfold row
  change _ < 2^10
  apply Nat.or_lt_two_pow
  · apply Nat.or_lt_two_pow
    · apply Nat.or_lt_two_pow
      · exact Nat.or_lt_two_pow (shifted_bound _ _ (digit_bound j 0) (by decide))
          (shifted_bound _ _ (digit_bound j 1) (by decide))
      · exact shifted_bound _ _ (digit_bound j 2) (by decide)
    · have h := digit_bound j 3; omega
  · exact shifted_bound _ _ (digit_bound j 4) (by decide)

theorem digit_value (j d : Nat) : digit j d = PV_CB3_WeightsDomain.digit j d := by
  unfold digit PV_CB3_WeightsDomain.digit
  rw [Nat.shiftRight_eq_div_pow]
  have hp : 2^(2*d) = 4^d := by rw [Nat.pow_mul]
  rw [hp]
  exact Nat.and_two_pow_sub_one_eq_mod _ 2
#print axioms digit_bound
#print axioms shifted_bound
#print axioms row_bound
#print axioms digit_value
end R1Z.PV_CB3_WeightsBits
