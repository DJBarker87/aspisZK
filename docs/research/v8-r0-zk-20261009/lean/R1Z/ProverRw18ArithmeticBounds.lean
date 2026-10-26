import R1Z.ProverRw18InlineContext
set_option autoImplicit false
namespace R1Z.ProverRw18ArithmeticBounds

-- Symbolic bounds for the native per-step arithmetic gates. In particular,
-- CM31's unreduced-sum product fits U64 on canonical limbs; no such bound is
-- silently inferred from the raw U32 carrier alone.
theorem product_bound (a b limit : Nat) (ha : a<limit) (hb : b<limit) :
    a*b<limit*limit := by
  by_cases zero : a=0
  · subst a
    simpa only [Nat.zero_mul] using Nat.mul_pos ha ha
  · exact (Nat.mul_lt_mul_of_pos_left hb (Nat.pos_of_ne_zero zero)).trans_le
      (Nat.mul_le_mul_right limit (Nat.le_of_lt ha))

theorem raw_scalar_product (a b : Nat) (ha : a<2^32) (hb : b<2^32) :
    a*b<2^64 := by
  have bound := product_bound a b (2^32) ha hb
  simpa only [← Nat.pow_add] using bound

theorem canonical_scalar_product (a b : Nat) (ha : a<2147483647) (hb : b<2147483647) :
    a*b<2^62 := by
  have bound := product_bound a b (2^31) (by omega) (by omega)
  simpa only [← Nat.pow_add] using bound

theorem canonical_sum (a b : Nat) (ha : a<2147483647) (hb : b<2147483647) :
    a+b<2^32 := by omega

theorem complex_product (a b c d : Nat)
    (ha : a<2147483647) (hb : b<2147483647)
    (hc : c<2147483647) (hd : d<2147483647) :
    (a+b)*(c+d)<2^64 :=
  raw_scalar_product (a+b) (c+d) (canonical_sum a b ha hb) (canonical_sum c d hc hd)

#print axioms product_bound
#print axioms raw_scalar_product
#print axioms canonical_scalar_product
#print axioms canonical_sum
#print axioms complex_product
end R1Z.ProverRw18ArithmeticBounds
