import NDE_MulStubValue
set_option autoImplicit false
namespace NDE_StubWordBounds
abbrev P : Nat := 2147483647

theorem product (a b : Nat) (ha : a < P) (hb : b < P) : a*b < 2^64 := by
  have h : a*b ≤ (P-1)*(P-1) := Nat.mul_le_mul (by omega) (by omega)
  norm_num [P] at h ⊢
  omega

theorem cross_product (a b c d : Nat) (ha : a < P) (hb : b < P)
    (hc : c < P) (hd : d < P) : (a+b)*(c+d) < 2^64 := by
  have h : (a+b)*(c+d) ≤ (2*(P-1))*(2*(P-1)) := Nat.mul_le_mul (by omega) (by omega)
  norm_num [P] at h ⊢
  omega

theorem sum (a b : Nat) (ha : a < P) (hb : b < P) : a+b < 2^64 := by
  norm_num [P] at ha hb ⊢
  omega

theorem subtract (a b : Nat) (ha : a < P) (hb : b < P) :
    b ≤ a+P ∧ a+P < 2^64 ∧ a+P-b < 2^64 := by
  norm_num [P] at ha hb ⊢
  omega

#print axioms product
#print axioms cross_product
#print axioms sum
#print axioms subtract
end NDE_StubWordBounds
