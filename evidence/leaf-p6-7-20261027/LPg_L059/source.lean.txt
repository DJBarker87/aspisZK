import LPg_StopRule
import LPc_Audit
set_option autoImplicit false
namespace LPg
/-- Arbitrarily many all-good iterations inhabit the loop invariant. -/
theorem good_prefix (n : Nat) : LPa.firstBad (fun _ => false) n = none := by
  apply (LPa.firstBad_none _ _).mpr
  intro i hi
  rfl
/-- Local witnesses for both continuations of the early-exit invariant. -/
theorem error_prefix (n : Nat) : LPa.firstBad (fun _ => true) (n+1) = some 0 := by
  apply first_error_sticky (fun _ => true) 1 (n+1) 0 (by omega)
  rfl
#print axioms good_prefix
#print axioms error_prefix
#print axioms LPc.Nonvacuity.boundary_inhabited
/-- Four canonical limb products fit below 2^64 before reduction. -/
theorem four_products (a b c d e f g h : Nat)
    (ha : a < 2147483647) (hb : b < 2147483647) (hc : c < 2147483647) (hd : d < 2147483647)
    (he : e < 2147483647) (hf : f < 2147483647) (hg : g < 2147483647) (hh : h < 2147483647) :
    a*h+b*g+c*f+d*e < 18446744073709551616 := by
  have h1 := Nat.mul_le_mul (Nat.le_of_lt ha) (Nat.le_of_lt hh)
  have h2 := Nat.mul_le_mul (Nat.le_of_lt hb) (Nat.le_of_lt hg)
  have h3 := Nat.mul_le_mul (Nat.le_of_lt hc) (Nat.le_of_lt hf)
  have h4 := Nat.mul_le_mul (Nat.le_of_lt hd) (Nat.le_of_lt he)
  omega
/-- The partial Mersenne fold bound is linear once the product bound is known. -/
theorem partial_fold (x : Nat) (hx : x < 2*2147483647*2147483647) :
    x%2147483648+x/2147483648 < 3*2147483647 := by omega
#print axioms four_products
#print axioms partial_fold
end LPg
