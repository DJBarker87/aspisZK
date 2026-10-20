import R22FastPairingRawRanges

set_option autoImplicit false

namespace AspisR1S5CurrentRepin

/-- Canonical 31-bit limbs make every one of the sixteen products in the
private Q raw routine fit the exact input cap used by the sequential R22
range proof.  This is the limb-to-product bridge; the separate source-trace
consumer applies `raw_ranges` to the actual multiplication witnesses. -/
theorem canonical_product_bound
    (a b c d e f g h : Nat)
    (ha : a ≤ 2^31 - 2) (hb : b ≤ 2^31 - 2)
    (hc : c ≤ 2^31 - 2) (hd : d ≤ 2^31 - 2)
    (he : e ≤ 2^31 - 2) (hf : f ≤ 2^31 - 2)
    (hg : g ≤ 2^31 - 2) (hh : h ≤ 2^31 - 2) :
    ∀ x ∈ [a*e,b*f,c*g,d*h,c*h,d*g,a*f,b*e,a*g,c*e,b*h,d*f,a*h,b*g,c*f,d*e],
      x ≤ (2^31 - 2)^2 := by
  intro x hx
  have hmem : x = a*e ∨ x = b*f ∨ x = c*g ∨ x = d*h ∨
      x = c*h ∨ x = d*g ∨ x = a*f ∨ x = b*e ∨
      x = a*g ∨ x = c*e ∨ x = b*h ∨ x = d*f ∨
      x = a*h ∨ x = b*g ∨ x = c*f ∨ x = d*e := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hx
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst x
  all_goals first
    | exact Nat.mul_le_mul ha he
    | exact Nat.mul_le_mul hb hf
    | exact Nat.mul_le_mul hc hg
    | exact Nat.mul_le_mul hd hh
    | exact Nat.mul_le_mul hc hh
    | exact Nat.mul_le_mul hd hg
    | exact Nat.mul_le_mul ha hf
    | exact Nat.mul_le_mul hb he
    | exact Nat.mul_le_mul ha hg
    | exact Nat.mul_le_mul hc he
    | exact Nat.mul_le_mul hb hh
    | exact Nat.mul_le_mul hd hf
    | exact Nat.mul_le_mul ha hh
    | exact Nat.mul_le_mul hb hg
    | exact Nat.mul_le_mul hc hf
    | exact Nat.mul_le_mul hd he

/-- Instantiating the checked R22 raw-range theorem with canonical limbs
closes all 18 sequential U64 wrapping guards. -/
theorem canonical_raw_range_guards
    (a b c d e f g h : Nat)
    (ha : a ≤ 2^31 - 2) (hb : b ≤ 2^31 - 2)
    (hc : c ≤ 2^31 - 2) (hd : d ≤ 2^31 - 2)
    (he : e ≤ 2^31 - 2) (hf : f ≤ 2^31 - 2)
    (hg : g ≤ 2^31 - 2) (hh : h ≤ 2^31 - 2) :
    let pp := (2^31-1)^2
    let u := AspisR1BatchedFoldArithmetic.fold (c*g + pp - d*h)
    let v := AspisR1BatchedFoldArithmetic.fold (c*h + d*g)
    c*g + pp < 2^64 ∧ d*h ≤ c*g + pp ∧ c*h + d*g < 2^64 ∧
    a*e + pp < 2^64 ∧ b*f ≤ a*e + pp ∧
    a*e + pp - b*f + 2*u < 2^64 ∧
    a*e + pp - b*f + 2*u + 3*(2^31-1) < 2^64 ∧
    v ≤ a*e + pp - b*f + 2*u + 3*(2^31-1) ∧
    a*f + b*e < 2^64 ∧ a*f + b*e + u < 2^64 ∧
    a*f + b*e + u + 2*v < 2^64 ∧
    a*g + c*e < 2^64 ∧ a*g + c*e + 2*pp < 2^64 ∧
    b*h ≤ a*g + c*e + 2*pp ∧ d*f ≤ a*g + c*e + 2*pp - b*h ∧
    a*h + b*g < 2^64 ∧ a*h + b*g + c*f < 2^64 ∧
    a*h + b*g + c*f + d*e < 2^64 ∧ 2*u < 2^64 ∧ 2*v < 2^64 := by
  have hproducts := canonical_product_bound a b c d e f g h ha hb hc hd he hf hg hh
  exact AspisR1.R22FastPairingRawRanges.raw_ranges
    (a*e) (b*f) (c*g) (d*h) (c*h) (d*g) (a*f) (b*e)
    (a*g) (c*e) (b*h) (d*f) (a*h) (b*g) (c*f) (d*e) hproducts

#print axioms canonical_product_bound
#print axioms canonical_raw_range_guards

end AspisR1S5CurrentRepin
