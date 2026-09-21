import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Natural-number bounds for the staged fused CM31 butterfly. These prove
absence of overflow/underflow in its stated arithmetic expressions, conditional
on canonical source limbs. They do not prove Rust extraction, reducer
correctness, FFT equivalence, a source entropy law or full privacy. -/
set_option autoImplicit false
namespace AspisV8R17.FusedButterfly

theorem canonical_product_bound (x y : ℕ)
    (hx : x < 2147483647) (hy : y < 2147483647) :
    x * y ≤ 4611686009837453316 := by
  have h := Nat.mul_le_mul (show x ≤ 2147483646 by omega)
    (show y ≤ 2147483646 by omega)
  norm_num at h
  exact h

/-- `p2` is P², not a field representative. The inequalities cover the
left-to-right source evaluation order, not merely the final residues. -/
theorem raw_bounds (u v a b c d : ℕ)
    (hu : u < 2147483647) (hv : v < 2147483647)
    (ha : a ≤ 4611686009837453316) (hb : b ≤ 4611686009837453316)
    (hc : c ≤ 4611686009837453316) (hd : d ≤ 4611686009837453316) :
    let p2 := 4611686014132420609
    b ≤ u + a + p2 ∧ a ≤ u + p2 ∧
    c ≤ v + 2*p2 ∧ d ≤ v + 2*p2 - c ∧
    u + a + p2 < 18446744073709551616 ∧
    u + p2 < 18446744073709551616 ∧
    v + c + d < 18446744073709551616 ∧
    u + p2 - a + b < 18446744073709551616 ∧
    v + 2*p2 < 18446744073709551616 ∧
    u + a + p2 - b < 9223372036854775808 ∧
    v + c + d < 9223372036854775808 ∧
    u + p2 - a + b < 9223372036854775808 ∧
    v + 2*p2 - c - d < 9223372036854775808 := by
  dsimp
  omega

theorem padding_is_prime_square :
    (4611686014132420609 : ℕ) = 2147483647 * 2147483647 := by
  norm_num

/-- Range bound for each limb of the scalar FMA used in the original merge
order. This is a bound, not a theorem about the source reducer's residue. -/
theorem scalar_fma_bound (acc x y : ℕ)
    (hacc : acc < 2147483647) (hx : x < 2147483647) (hy : y < 2147483647) :
    acc + x * y < 4611686018427387904 := by
  have h := canonical_product_bound x y hx hy
  omega

#print axioms canonical_product_bound
#print axioms raw_bounds
#print axioms padding_is_prime_square
#print axioms scalar_fma_bound
end AspisV8R17.FusedButterfly
