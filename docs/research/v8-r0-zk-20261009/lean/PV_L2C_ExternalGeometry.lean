import PV_L2C_HashRange
set_option autoImplicit false
namespace PV_L2C_ExternalGeometry

/-- Every native chunks_exact_mut(4) group has precisely these four offsets. -/
theorem group_bounds (b l : Nat) (hb : b < 4) (hl : l < 4) :
    4*b+l < 16 ∧ 4*b ≤ 4*b+l ∧ 4*b+l < 4*(b+1) := by omega
#print axioms group_bounds

theorem disjoint_groups (b c l k : Nat) (hb : b ≠ c) (hl : l < 4) (hk : k < 4) :
    4*b+l ≠ 4*c+k := by omega
#print axioms disjoint_groups

theorem column_mask (i : Nat) : i &&& 3 = i % 4 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod i 2
#print axioms column_mask

/-- All native and owned matrix partial sums fit in u64, including raw U32
inputs. No canonical-input assumption is needed for this external layer. -/
theorem matrix_bounds (a b c d : Nat) (ha : a < 2^32) (hb : b < 2^32)
    (hc : c < 2^32) (hd : d < 2^32) :
    2*a+3*b+c+d < 2^62 ∧ a+2*b+3*c+d < 2^62 ∧
    a+b+2*c+3*d < 2^62 ∧ 3*a+b+c+2*d < 2^62 := by omega
#print axioms matrix_bounds

theorem lane_bound (a b c d e : Nat) (ha : a < 2147483647)
    (hb : b < 2147483647) (hc : c < 2147483647)
    (hd : d < 2147483647) (he : e < 2147483647) :
    a+(b+c+d+e) < 2^62 := by omega
#print axioms lane_bound

theorem sum_four (a b c d : Nat) : [a,b,c,d].sum = a+b+c+d := by
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
  omega
#print axioms sum_four
end PV_L2C_ExternalGeometry
