import R1Z.PV_Join_RadixBounds5
set_option autoImplicit false
namespace R1Z.PV_Join_SquareBounds5
open PV_Join_Canonical5

theorem subtraction_safe (a b : Nat) (hb : b<P) : b ≤ a+P := by omega
theorem sum_bound (a b : Nat) (ha : a<P) (hb : b<P) : a+b < 2^32 := by
  change a<2147483647 at ha
  change b<2147483647 at hb
  omega
theorem difference_bound (a b : Nat) (ha : a<P) : a+P-b < 2^32 := by
  change a<2147483647 at ha
  change a+2147483647-b < 4294967296
  omega
theorem product_bound (a b : Nat) (ha : a<P) (hb : b<P) :
    (a+b)*(a+P-b) < 2^64 := by
  by_cases hz : a+b=0
  · rw [hz,Nat.zero_mul]; norm_num
  · have p := Nat.mul_lt_mul_of_pos_left (difference_bound a b ha) (by omega : 0<a+b)
    have q := Nat.mul_le_mul_right (2^32) (Nat.le_of_lt (sum_bound a b ha hb))
    exact p.trans_le (by simpa only [← Nat.pow_add] using q)

#print axioms subtraction_safe
#print axioms sum_bound
#print axioms difference_bound
#print axioms product_bound
end R1Z.PV_Join_SquareBounds5
