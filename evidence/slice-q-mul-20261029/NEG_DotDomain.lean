import NEG_RowDomain
set_option autoImplicit false
namespace NEG_DotDomain
abbrev P : Nat := 2147483647
abbrev B : Nat := 4611686009837453316
/-- Arbitrary partial batch, including the fourth term. -/
theorem term_safe (n old product : Nat) (hn : n < 4)
    (ho : old ≤ n*B) (hp : product ≤ B) : old+product < 2^64 := by
  have : n ≤ 3 := by omega
  have h := Nat.mul_le_mul_right B this
  norm_num [B] at h hp ho ⊢
  omega
/-- Invariant preserved by one nondeterministic product step. -/
theorem term_invariant (n old product : Nat)
    (ho : old ≤ n*B) (hp : product ≤ B) : old+product ≤ (n+1)*B := by
  rw [Nat.add_mul]; omega
/-- Products over the canonical input domain are admitted by the bounded oracle. -/
theorem instantiate (a b : Nat) (ha : a<P) (hb : b<P) : a*b ≤ B :=
  NEG_RowDomain.product_bound a b ha hb
/-- All arbitrary u64 sums fold below 2^34, so the stronger batch bound is unnecessary. -/
theorem fold_bound (sum : Nat) (h : sum < 2^64) :
    sum % 2^31 + sum / 2^31 < 2^34 := by
  have hm := Nat.mod_lt sum (show 0<2^31 by decide)
  have hd : sum/2^31 < 2^33 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by norm_num at *; omega)
  omega
/-- Seven folded batches fit the existing reduce_u64 domain. -/
theorem accumulated (n old folded : Nat) (hn : n < 7)
    (ho : old < (n+1)*2^34) (hf : folded < 2^34) :
    old+folded < (n+2)*2^34 ∧ old+folded < 2^37 := by
  have h := Nat.mul_le_mul_right (2^34) (show n+2≤8 by omega)
  constructor
  · rw [Nat.add_mul] at *; omega
  · norm_num at h; omega
/-- Every base-scalar read is in the same original 608-byte carrier. -/
theorem scalar_window (slot term : Nat) (hs : slot<4) (ht : term<26) :
    slot*120+term*4+4 ≤ 608 := by omega
/-- All three extension-scalar tails are in the original carrier. -/
theorem tail_windows (slot : Nat) (hs : slot<4) :
    slot*120+120≤608 ∧ 480+slot*32+16≤608 ∧ 480+slot*32+32≤608 := by omega
#print axioms term_safe
#print axioms term_invariant
#print axioms instantiate
#print axioms fold_bound
#print axioms accumulated
#print axioms scalar_window
#print axioms tail_windows
end NEG_DotDomain
