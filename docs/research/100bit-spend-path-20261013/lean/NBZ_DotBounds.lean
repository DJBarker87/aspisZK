import NBW_Audit
set_option autoImplicit false
namespace NBZ_DotBounds
abbrev P2 : Nat := (2^31-2)^2
def sumProducts : List (Nat×Nat) → Nat
 | [] => 0
 | (a,b)::xs => a*b+sumProducts xs
/-- Only the canonical product bound is used; no field multiplication is
unfolded or evaluated by the kernel. -/
theorem product_bound (a b : Nat) (ha : a<2^31-1) (hb : b<2^31-1) : a*b≤P2 := by
 have h := Nat.mul_le_mul (show a≤2^31-2 by omega) (show b≤2^31-2 by omega)
 simpa only [P2,pow_two] using h
/-- Bounds follow the SAME decoded product list, not independently chosen sums. -/
theorem sum_bound (xs : List (Nat×Nat))
 (canonical : ∀ x ∈ xs, x.1<2^31-1 ∧ x.2<2^31-1) :
 sumProducts xs≤xs.length*P2 := by
 induction xs with
 | nil => simp only [sumProducts,List.length_nil,Nat.zero_mul,Nat.le_refl]
 | cons x xs ih =>
   have hx := canonical x List.mem_cons_self
   have hp := product_bound x.1 x.2 hx.1 hx.2
   have ht := ih (by intro y hy;exact canonical y (List.mem_cons_of_mem _ hy))
   simp only [sumProducts,List.length_cons,Nat.succ_mul]
   omega
/-- The native group has at most four products, including the final two-term
window. Its exact integer sum fits U64 before the one Mersenne fold. -/
theorem group_safe (xs : List (Nat×Nat)) (size : xs.length≤4)
 (canonical : ∀ x ∈ xs, x.1<2^31-1 ∧ x.2<2^31-1) :
 sumProducts xs<2^64 ∧ AspisR1BatchedFoldSourceStep.fold (sumProducts xs)<2^34 := by
 have h := sum_bound xs canonical
 have count := Nat.mul_le_mul_right P2 size
 have safe : sumProducts xs<2^64 := by norm_num [P2] at count h ⊢;omega
 exact ⟨safe,AspisR1BatchedFoldSourceStep.fold_lt_two34 safe⟩
/-- Seven folded groups fit the retained prefix limb accumulator. -/
theorem folded_sum (groups : List Nat) (size : groups.length≤7)
 (small : ∀ x∈groups,x<2^34) : groups.sum<2^37 := by
 have bound : groups.sum≤groups.length*(2^34-1) := by
   induction groups with
   | nil => simp
   | cons x xs ih =>
     have hx := small x List.mem_cons_self
     have ht := ih (by simp only [List.length_cons] at size;omega)
       (by intro y hy;exact small y (List.mem_cons_of_mem _ hy))
     simp only [List.sum_cons,List.length_cons,Nat.succ_mul]
     omega
 have count := Nat.mul_le_mul_right (2^34-1) size
 omega
#print axioms product_bound
#print axioms sum_bound
#print axioms group_safe
#print axioms folded_sum
end NBZ_DotBounds
