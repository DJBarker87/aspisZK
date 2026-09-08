import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
/-! Symbolic interfaces for research arithmetic rewrites; not translated Rust.
The parser supplies canonical limbs. Every fresh four-product accumulator and
all its prefixes fit u64; the seven reduced chunks fit u64 separately. -/
namespace AspisV8.ArithmeticRewrites
open scoped BigOperators
theorem grouped_linear {K I : Type*} [CommRing K]
    (s : Finset I) (a b c : K) (x y z : I → K) :
    (∑ i ∈ s, (a*x i + b*y i + c*z i)) =
      a*(∑ i ∈ s, x i) + b*(∑ i ∈ s, y i) + c*(∑ i ∈ s, z i) := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

def limbMax : Nat := 2147483646
theorem four_max : 4 * limbMax^2 < 2^64 := by norm_num [limbMax]
theorem canonical_product {a b : Nat} (ha : a ≤ limbMax) (hb : b ≤ limbMax) :
    a*b ≤ limbMax^2 := by simpa [pow_two] using Nat.mul_le_mul ha hb

theorem four_prefix (x y : Fin 4 → Nat)
    (hx : ∀ i, x i ≤ limbMax) (hy : ∀ i, y i ≤ limbMax)
    (s : Finset (Fin 4)) :
    (∑ i ∈ s, x i*y i) < 2^64 := by
  have hsum : (∑ i ∈ s, x i*y i) ≤ s.card * limbMax^2 := by
    calc
      _ ≤ ∑ _i ∈ s, limbMax^2 := Finset.sum_le_sum (fun i _ => canonical_product (hx i) (hy i))
      _ = _ := by simp
  have hc : s.card ≤ 4 := by
    simpa using Finset.card_le_card (Finset.subset_univ s)
  have hm := Nat.mul_le_mul_right (limbMax^2) hc
  exact lt_of_le_of_lt (hsum.trans hm) four_max

theorem wrapping_prefix_exact (x y : Fin 4 → Nat)
    (hx : ∀ i, x i ≤ limbMax) (hy : ∀ i, y i ≤ limbMax)
    (s : Finset (Fin 4)) :
    (∑ i ∈ s, x i*y i) % 2^64 = ∑ i ∈ s, x i*y i :=
  Nat.mod_eq_of_lt (four_prefix x y hx hy s)

theorem seven_reduced_chunks (x : Fin 7 → Nat) (hx : ∀ i, x i ≤ limbMax) :
    (∑ i, x i) < 2^64 := by
  have hs : (∑ i, x i) ≤ 7*limbMax := by
    calc
      _ ≤ ∑ _i : Fin 7, limbMax := Finset.sum_le_sum (fun i _ => hx i)
      _ = _ := by simp
  have hb : 7*limbMax < 2^64 := by norm_num [limbMax]
  exact lt_of_le_of_lt hs hb
#print axioms grouped_linear
#print axioms four_prefix
#print axioms wrapping_prefix_exact
#print axioms seven_reduced_chunks
end AspisV8.ArithmeticRewrites
