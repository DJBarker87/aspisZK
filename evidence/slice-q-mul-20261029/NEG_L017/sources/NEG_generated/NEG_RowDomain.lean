import NEG_ProductAbstraction
set_option autoImplicit false
namespace NEG_RowDomain
/-- Phase-three bound retained by the frozen batching schedule. -/
def Bound (row : Nat) : Prop :=
  row ≤ 17179869183 + 3 * (2147483646 * 2147483646)

theorem product_bound (a b : Nat) (ha : a < 2147483647) (hb : b < 2147483647) :
    a*b ≤ 2147483646*2147483646 := by
  exact Nat.mul_le_mul (by omega) (by omega)

theorem checked_add_safe (row a b : Nat) (hr : Bound row)
    (ha : a < 2147483647) (hb : b < 2147483647) :
    row + a*b < 2^64 := by
  have hp := product_bound a b ha hb
  unfold Bound at hr
  omega

theorem u64_product_exact (a b : Nat) (ha : a < 2147483647) (hb : b < 2147483647) :
    NEG_ProductAbstraction.machineProduct 64 a b = a*b := by
  have hp := product_bound a b ha hb
  unfold NEG_ProductAbstraction.machineProduct
  exact Nat.mod_eq_of_lt (by omega)

theorem u128_product_exact (a b : Nat) (ha : a < 2147483647) (hb : b < 2147483647) :
    NEG_ProductAbstraction.machineProduct 128 a b = a*b := by
  have hp := product_bound a b ha hb
  unfold NEG_ProductAbstraction.machineProduct
  exact Nat.mod_eq_of_lt (by omega)

/-- A product oracle constrained only by this upper bound over-approximates
all canonical native products. No exact-product assumption enters Kani. -/
theorem bounded_oracle_admissible (a b : Nat)
    (ha : a < 2147483647) (hb : b < 2147483647) :
    ∃ p, p ≤ 2147483646*2147483646 ∧ p=a*b :=
  ⟨a*b,product_bound a b ha hb,rfl⟩

#print axioms product_bound
#print axioms checked_add_safe
#print axioms u64_product_exact
#print axioms u128_product_exact
#print axioms bounded_oracle_admissible
end NEG_RowDomain
